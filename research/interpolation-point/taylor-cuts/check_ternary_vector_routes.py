from itertools import product
from random import Random
from ternary_vector_routes import solve

def check(n,edges,b):
    labels=set()
    def visit(u,seen,t):
        if u==n:
            labels.add(t)
            return
        for a,v,g in edges:
            if a==u and v not in seen:
                visit(u+1,seen|{v},tuple((x+y)%3 for x,y in zip(t,g)))
    visit(0,set(),(0,)*b)
    for t in product(range(3),repeat=b):
        s,ids,stats=solve(2*n,edges,t,threshold=1)
        assert (s=='SAT')==(t in labels) and s!='UNKNOWN',(edges,t,s)
        if ids is not None:
            assert sorted(v for i in ids for v in edges[i][:2])==list(range(2*n))
    return len(tuple(product(range(3),repeat=b)))

if __name__=='__main__':
    rng=Random(244)
    cases=0
    for j in range(32):
        n=rng.randrange(1,5)
        b=1+j%2
        edges=[(i,n+i,(0,)*b) for i in range(n)]
        for u,v in product(range(n),repeat=2):
            if rng.randrange(4)==0:
                edges.append((u,v+n,tuple(rng.randrange(3) for _ in range(b))))
        cases+=check(n,edges,b)
    n=6
    # Exactly three disjoint two-vector bases trigger the sharpened bound.
    edges=[(i,n+i,((1,0) if i%2 else (0,1))) for i in range(n)]
    edges += [(i,n+i,(0,0)) for i in range(n)]
    status,ids,stats=solve(2*n,edges,(2,2),threshold=1)
    assert status=='SAT' and stats['bases']==1
    assert solve(2,[(0,1,(1,)),(0,1,(0,))],(2,),threshold=1,portal_cap=0)[0]=='UNKNOWN'
    print(cases,'brute target checks plus basis and cap controls passed')
