from random import Random
from itertools import product
from functools import reduce
from operator import xor

def span(xs):
    d={0}
    for x in xs:d|={u^x for u in d}
    return d

def tagged(g,x):
    return reduce(xor,(g[i] for i in range(len(g)) if x>>i&1),0)

def summed(mask,vals):
    return reduce(xor,(v for i,v in enumerate(vals) if mask>>i&1),0)

def outside_keys(keys, part):
    a=span(k for i,k in enumerate(keys) if part>>i&1)
    b=span(k for i,k in enumerate(keys) if not part>>i&1)
    return sorted(a&b)

def wedge(u,v,n):
    return sum((((u>>i&1)*(v>>j&1))^((u>>j&1)*(v>>i&1)))<<(j*(j-1)//2+i) for j in range(n) for i in range(j))

def insert(piv,vec,record):
    y=vec
    while y and (b:=y.bit_length()-1) in piv:y^=piv[b][0]
    if y:piv[y.bit_length()-1]=y,record

def test(rows):
    n=len(rows); d=2; keys,tags,heights=zip(*rows)
    charts=list(product(range(4),repeat=d)); masks=range(1<<n)
    active=lambda g:sum((tagged(g,k)==t)<<i for i,(k,t,_) in enumerate(rows))
    locals_=[{u for u in masks if u&~active(g)==0 and summed(u,keys)==0} for g in charts]
    physical=any(len(span(summed(u,heights) for u in l))==4 for l in locals_)
    graphW={wedge(u,v,n) for l in locals_ for u in l for v in l}
    exact=span(graphW)
    feasible_rel=set.union(*locals_)
    L=span(feasible_rel)
    forced=False
    for u in L:
        h=summed(u,heights)
        if not h or not any(u&~active(g)==0 for g in charts):continue
        vals=[(k<<3)|(t<<1)|int(bool(v and v!=h)) for k,t,v in rows]
        forced_span=span(v for i,v in enumerate(vals) if u>>i&1)
        trace=forced_span & set(range(8))
        assert trace in ({0},{0,1})
        if trace=={0,1}:
            forced=True;break
        reduceq=lambda x:min(x^s for s in forced_span)
        if any((span(reduceq(v) for i,v in enumerate(vals) if b>>i&1 and not(u>>i&1)) & {reduceq(z) for z in range(8)})=={0,reduceq(1)} for b in masks):
            forced=True;break
    assert forced==physical
    def DP(ids):
        part=sum(1<<i for i in ids);boundary=outside_keys(keys,part);gr={}
        def add(ch,p,q,u,v):
            z=wedge(u,v,n)
            insert(gr.setdefault((ch,p,q),{}),1|(u<<1)|(v<<(n+1))|(z<<(2*n+1)),(u,v))
        if len(ids)==1:
            i=ids[0];bit=1<<i
            for g in charts:
                ch=tuple(tagged(g,x) for x in boundary)
                choices=(0,bit) if active(g)&bit else (0,)
                for u,v in product(choices,repeat=2):
                    p=summed(u,keys);q=summed(v,keys)
                    if p in boundary and q in boundary:add(ch,p,q,u,v)
        else:
            cut=len(ids)//2;left,bl=DP(ids[:cut]);right,br=DP(ids[cut:])
            for (l,p,q),reps in left.items():
                for (r,s,t),other in right.items():
                    if p^s not in boundary or q^t not in boundary:continue
                    if any(l[bl.index(x)]!=r[br.index(x)] for x in set(bl)&set(br)):continue
                    def val(x):
                        a=next(a for a in bl if x^a in br)
                        return l[bl.index(a)]^r[br.index(x^a)]
                    ch=tuple(val(x) for x in boundary)
                    for _,(u,v) in reps.values():
                        for _,(y,z) in other.values():add(ch,p^s,q^t,u^y,v^z)
        return gr,boundary
    root,_=DP(list(range(n)));zz=[]
    for _,(u,v) in root[((0,),0,0)].values():
        assert any(u in l and v in l for l in locals_)
        zz.append(wedge(u,v,n))
    assert span(zz)==exact

rng=Random(20523)
cases=[[(1,0,0),(1,0,1),(1,1,0),(1,1,2)],[(1,0,0),(1,0,1),(2,1,0),(2,1,2)]]
for _ in range(240):cases.append([(rng.randrange(4),rng.randrange(4),rng.randrange(4)) for i in range(6)])
for c in cases:test(c)
print(len(cases),'joint forced-quotient / balanced-tree / actual-root-traceback cases passed')
