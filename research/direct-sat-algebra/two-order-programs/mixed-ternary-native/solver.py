"""Raw 3CNF SAT via affine scope extraction and a bounded ternary transversal."""
from collections import defaultdict
from itertools import product
from pathlib import Path
import sys
from time import perf_counter_ns
root=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(root/'guard-cap-review/cnf-common-tables'))
from route import Basis,binary_model
sys.path.insert(0,str(root/'direct-sat-portfolio'))
from affine_quotient import _gauss,_restrict,_mul
from original_cnf import accepts_cnf


def bits(x):
    while x:
        b=x&-x
        yield b.bit_length()-1
        x^=b


def parity(x):return x.bit_count()&1


def chart(n,eqs):
    basis=Basis()
    if any(not basis.add(a,b) for a,b in eqs):return None
    free=[i for i in range(n) if i not in basis.rows]
    pos={v:i for i,v in enumerate(free)}
    forms=[]
    for i in range(n):
        if i in pos:forms.append(2<<pos[i]);continue
        a,b=basis.rows[i]
        for j in bits(a^(1<<i)):b ^= forms[j]
        forms.append(b)
    return len(free),forms


def sub(f,forms):
    out=f&1
    for j in bits(f>>1):out ^= forms[j]
    return out


def lift(forms,x):
    word=1|(x<<1)
    return sum(parity(f&word)<<i for i,f in enumerate(forms))


def span(vecs):
    out={0}
    for v in vecs:out |= {x^v for x in out}
    return out


def discover(normals,S,limit,cost):
    cost['search_nodes']+=1
    def reduce(x):
        for pivot in sorted(S,reverse=True):
            if x>>pivot&1:x ^= S[pivot]
        return x
    for triple in normals:
        U=span(triple)
        if len(U)==8 and all(reduce(u) for u in U if u):
            if not limit:return None
            for u in sorted(U-{0}):
                v=reduce(u)
                found=discover(normals,{**S,v.bit_length()-1:v},limit-1,cost)
                if found is not None:return [u]+found
            return None
    return []


def block_cover(normals,limit):
    spaces=list({frozenset(span(row)) for row in normals if len(span(row))==8})
    parent=list(range(len(spaces)))
    def root(i):
        while i!=parent[i]:
            parent[i]=parent[parent[i]];i=parent[i]
        return i
    for i,U in enumerate(spaces):
        for j in range(i):
            if len(U & spaces[j])>1:parent[root(i)]=root(j)
    components={}
    for i,U in enumerate(spaces):
        k=root(i)
        components[k]=components[k]&U if k in components else U
    cover=[]
    basis=Basis()
    for common in components.values():
        if len(common)!=2:return None
        u=next(x for x in common if x)
        before=len(basis.rows);basis.add(u,0)
        if len(basis.rows)==before:return None
        cover.append(u)
    if len(cover)>limit:return None
    # Each component contributed its own common nonzero member, so all its spaces drop rank.
    return cover


def affine_anf(f):
    return ({0} if f&1 else set())|{1<<i for i in bits(f>>1)}


def substitute(p,forms):
    result=set()
    for t in p:
        term={0}
        for i in bits(t):term=_mul(term,affine_anf(forms[i]))
        result ^= term
    return result


def reduce_eqs(eqs):
    basis={}
    for p in eqs:
        p=set(p)
        while p:
            t=max(p,key=lambda x:(x.bit_count(),x))
            if t not in basis:
                basis[t]=p;break
            p ^= basis[t]
    return list(basis.values())


def terminal(r,eqs,cap,cost):
    layers=[]
    while True:
        eqs=reduce_eqs(eqs)
        linears=[(sum(t for t in p if t),int(0 in p)) for p in eqs if all(t.bit_count()<=1 for t in p)]
        if not linears:break
        mapped=chart(r,linears)
        if mapped is None:return 'unsat',None
        r,forms=mapped
        layers.append(forms)
        eqs=[substitute(p,forms) for p in eqs]
    q=len(eqs)
    cost.update(residual_bits=r,equations=q)
    if min(r,q)>cap:return 'skip',None
    if r<=q:
        cost.update(method='enumeration',evaluations=0)
        for x in range(1<<r):
            cost['evaluations']+=1
            if all(not(sum((x&t)==t for t in p)&1) for p in eqs):break
        else:return 'unsat',None
    else:
        cost.update(method='quadratic_gauss',gauss_calls=0)
        def count(fixed,x):
            restricted=[_restrict(p,fixed,x) for p in eqs]
            total=0;phase=set()
            for i in range(1<<q):
                if i:phase ^= restricted[(i&-i).bit_length()-1]
                total+=_gauss(phase,r-fixed.bit_count())
            cost['gauss_calls']+=1<<q
            value,rem=divmod(total,1<<q)
            if rem or value<0:raise AssertionError('invalid Gauss count')
            return value
        x=0
        if count(0,0)==0:return 'unsat',None
        for j in range(r):
            if not count((2<<j)-1,x):x |= 1<<j
    for forms in reversed(layers):x=lift(forms,x)
    return 'sat',x


def oriented_chart(r,forms,clauses):
    """Choose coset coordinates from literal normals, preferring binary exterior rows."""
    basis={}
    selected=0
    def reduce(v):
        coeff=0
        while v:
            pair=basis.get(v.bit_length()-1)
            if pair is None:break
            row,carry=pair
            v ^= row;coeff ^= carry
        return v,coeff
    rows=sorted(clauses,key=lambda c:len(c)>2)
    def candidates():
        for row in rows:
            for f in row:yield sub(f,forms)>>1
        for i in range(r):yield 1<<i
    for v in candidates():
        rem,coeff=reduce(v)
        if rem:
            basis[rem.bit_length()-1]=(rem,coeff^(1<<selected))
            selected+=1
        if selected==r:break
    old_in_new=[reduce(1<<i)[1]<<1 for i in range(r)]
    return [sub(f,old_in_new) for f in forms]


def solve(n,clauses,*,b=1,extract_arities=(1,2,3),exponent_cap=12,complete=False,orient=False,detect_blocks=False):
    start=perf_counter_ns()
    if any(type(i) is not int or i<0 for i in (n,b,exponent_cap)):raise ValueError('invalid limits')
    arities=set(extract_arities)
    if not arities<={0,1,2,3}:raise ValueError('unsupported extraction arity')
    raw=tuple(tuple(c) for c in clauses)
    if any(type(l) is not int or not 1<=abs(l)<=n for c in raw for l in c):raise ValueError('invalid literal')
    cost=dict(raw_n=n,raw_clauses=len(raw),cells=0,groups={},extract_arities=sorted(arities),
              search_nodes=0,cosets=[],fallback_evaluations=0)
    def finish(status,route,x=None):
        if status=='sat' and not (type(x) is int and 0<=x<1<<n and accepts_cnf(raw,x)):
            raise RuntimeError('original CNF replay failed')
        cost['elapsed_ns']=perf_counter_ns()-start
        return dict(status=status,route=route,witness=x,cost=cost)
    def fallback(reason):
        if not complete:return finish('skip',reason)
        for x in range(1<<n):
            cost['fallback_evaluations']+=1
            if accepts_cnf(raw,x):return finish('sat','raw_fallback',x)
        return finish('unsat','raw_fallback')
    groups=defaultdict(dict)
    for row in raw:
        c=set(row)
        if any(-x in c for x in c):continue
        scope=tuple(sorted(abs(l)-1 for l in c))
        if len(scope)>3:return fallback('width')
        forbid=sum((-(j+1) in c)<<i for i,j in enumerate(scope))
        groups[scope][forbid]=tuple(sorted(c))
    eqs=[];residual=[]
    for scope,patterns in groups.items():
        size=1<<len(scope);cost['cells']+=size
        ar=len(scope);cost['groups'][ar]=cost['groups'].get(ar,0)+1
        valid=[x for x in range(size) if x not in patterns]
        if not valid:return finish('unsat','empty_group')
        if ar in arities:
            normals=[u for u in range(1,size) if all(not parity(u&(x^valid[0])) for x in valid)]
            for u in normals:
                eqs.append((sum(1<<scope[i] for i in bits(u)),parity(u&valid[0])))
            if len(valid)*(len(normals)+1)==size:continue
        residual.extend(patterns.values())
    mapped=chart(n,eqs)
    if mapped is None:return finish('unsat','affine_contradiction')
    d,raw_forms=mapped
    clauses=[tuple(raw_forms[abs(l)-1]^int(l>0) for l in row) for row in residual]
    cost.update(chart_dimension=d,residual_clauses=len(clauses))
    normals=[tuple(f>>1 for f in row) for row in clauses]
    cover=block_cover(normals,b) if detect_blocks else None
    cost['cover_method']='scope_intersections' if cover is not None else 'branch_search'
    if cover is None:cover=discover(normals,{},b,cost)
    if cover is None:return fallback('no_transversal')
    cost['cover']=cover
    unresolved=False
    for value in range(1<<len(cover)):
        r,forms=chart(d,[(u,(value>>j)&1) for j,u in enumerate(cover)])
        if orient:forms=oriented_chart(r,forms,clauses)
        polys=[];binary=True;twocnf=[]
        for clause in clauses:
            p={0}
            for f in clause:p=_mul(p,affine_anf(sub(f,forms)))
            if any(t.bit_count()>2 for t in p):raise AssertionError('uncovered cubic')
            polys.append(p)
            support=0
            for t in p:support |= t
            if support.bit_count()>2:binary=False;continue
            ids=list(bits(support))
            for vals in product((0,1),repeat=len(ids)):
                x=sum(v<<j for j,v in zip(ids,vals))
                if sum((x&t)==t for t in p)&1:twocnf.append(tuple(-(j+1) if v else j+1 for j,v in zip(ids,vals)))
        rec=dict(coset=value,bits=r,oriented=orient)
        cost['cosets'].append(rec)
        if binary:
            rec.update(method='2sat',rows=len(twocnf))
            x=binary_model(r,twocnf);status='unsat' if x is None else 'sat'
        else:status,x=terminal(r,polys,exponent_cap,rec)
        rec['status']=status
        if status=='sat':return finish(status,'transversal',lift(raw_forms,lift(forms,x)))
        unresolved |= status=='skip'
    return fallback('coset_cap') if unresolved else finish('unsat','transversal')
