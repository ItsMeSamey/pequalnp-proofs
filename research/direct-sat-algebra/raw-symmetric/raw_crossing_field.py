"""Discover a scalar field and symmetric coordinates on a recovered leaf crossing."""
from itertools import combinations
from extension_field_target import centroid,pack,unpack
from hidden_product_network import encoder
from punctured_witness import BinaryField
from quadratic_centroid import independent,zero_combinations
from quadratic_target import apply_basis,evaluate_anf,insert,reduce_vector
from raw_symmetric_leaves import recover as discover_leaves
from raw_symmetric_overlap import fit
from untwisted_field_coordinates import module_basis,scale


def _candidates(space,limit):
    count=0
    for x in space:
        if count>=limit: return
        yield x
        count+=1
    for mask in range(1,1<<len(space)):
        if count>=limit: return
        if mask.bit_count()>1:
            yield apply_basis(space,mask)
            count+=1


def recover(n,m,constant,linear,pairs,*,degree=None,max_trials=256,leaf=None):
    """Result is verified by fit. Degree refers to one proper scalar subfield."""
    if n!=2*m or max_trials<1: return None
    if leaf is None:
        leaf=discover_leaves(n,m,constant,linear,pairs,max_pairing_trials=max_trials)
    if leaf is None: return None
    leaves=leaf.leaves
    _,centers,_=leaf.pairing
    def raw(x): return evaluate_anf(constant,linear,pairs,x)
    def crossing(u,v): return raw(u)^raw(v)^raw(u^v)^constant
    cross={(i,m+j):crossing(u,v) for i,u in enumerate(centers) for j,v in enumerate(leaves)}
    actions=centroid(n,m,cross)
    if not actions: return None
    split=n*n
    def join(s,t): return pack(s,n)|(pack(t,m)<<split)
    def decode(x): return unpack(x,n),unpack(x>>split,m)
    def compose(a,b):
        s,t=decode(a)
        v,w=decode(b)
        return join([apply_basis(s,x) for x in v],[apply_basis(t,x) for x in w])
    space=tuple(join(s,t) for s,t in actions)
    one=join([1<<i for i in range(n)],[1<<i for i in range(m)])
    for k in ([degree] if degree is not None else range(2,m//2+1)):
        if k<2 or m%k or m//k<2: continue
        def frob_defect(a):
            v=a
            for _ in range(k): v=compose(v,v)
            return v^a
        fixed=zero_combinations(space,frob_defect)
        for alpha in _candidates(fixed,max_trials):
            powers=[]
            pivot={}
            v=one
            for j in range(k):
                if not insert(v,1<<j,pivot): break
                powers.append(v)
                v=compose(v,alpha)
            if len(powers)!=k: continue
            rest,rel=reduce_vector(v,pivot)
            if rest: continue
            try: f=BinaryField((1<<k)|rel)
            except ValueError: continue
            maps=[decode(x) for x in powers]
            dom=module_basis(n,[s for s,t in maps])
            ob=module_basis(m,[t for s,t in maps])
            if not dom or not ob: continue
            if any(v>>m for v in dom[:m]) or any(v&((1<<m)-1) for v in dom[m:]):
                continue
            fc=tuple(apply_basis(centers,v) for v in dom[:m])
            fl=tuple(apply_basis(leaves,v>>m) for v in dom[m:])
            r=m//k
            encode=encoder(ob)
            pencil=[tuple(encode(crossing(fc[i*k],fl[j*k])) for j in range(r)) for i in range(r)]
            def act(X,y):
                val=0
                for j in range(r):
                    col=(X>>(m*j))&((1<<m)-1)
                    val ^= scale(f,(y>>(k*j))&(f.size-1),col)
                return val
            def defect(X):
                g=0
                for cols in pencil:
                    cols=[act(X,v) for v in cols]
                    for i,j in combinations(range(r),2):
                        g=(g<<k)|(((cols[j]>>(k*i))^(cols[i]>>(k*j)))&(f.size-1))
                return g
            sym=zero_combinations((1<<j for j in range(m*r)),defect)
            for X in _candidates(sym,max_trials):
                cols=[act(X,1<<j) for j in range(m)]
                if len(independent(cols))!=m: continue
                inv=encoder(cols)
                output=[apply_basis(ob,inv(1<<j)) for j in range(m)]
                def groups(seq): return [seq[j:j+k] for j in range(0,m,k)]
                result=fit(f,groups(fc),groups(fl),groups(output),constant,linear,pairs)
                if result is not None: return result
    return None
