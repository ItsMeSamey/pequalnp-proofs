from itertools import combinations, product
from random import Random
from labelled_konig_deficiency import solve


def labels(n,edges,b):
    def visit(rem):
        if not rem:
            return {(0,)*b}
        u=min(rem)
        out=set()
        for a,c,g in edges:
            if u in (a,c) and a in rem and c in rem:
                out.update(tuple((x+y)%3 for x,y in zip(t,g)) for t in visit(rem-{a,c}))
        return out
    return visit(set(range(n)))

if __name__=='__main__':
    rng=Random(612)
    calls=0
    for j in range(45):
        n=2*rng.randrange(1,5)
        b=1+j%2
        es=[(u,v,tuple(rng.randrange(3) for _ in range(b))) for u,v in combinations(range(n),2) if rng.randrange(3)]
        expected=labels(n,es,b)
        for t in product(range(3),repeat=b):
            status,ids,d=solve(n,es,t)
            assert (status=='SAT')==(t in expected) and status!='UNKNOWN'
            calls+=1
    # Complete split host: independent shore 2 and clique shore 6 imply deficiency 2.
    es=[(u,v,(0,)) for u,v in combinations(range(8),2) if v>=2]
    for u,v in combinations(range(2,8),2):
        es.extend([(u,v,(1,)),(u,v,(2,))])
    for t in range(3):
        status,w,d=solve(8,es,(t,),deficiency_cap=2)
        assert status=='SAT' and d['deficiency']==2
        assert sum(es[i][0]>=2 for i in w)==2
    assert solve(8,es,(0,),deficiency_cap=1)[0]=='UNKNOWN'
    # A residue-impossible sparse instance can exhaust the vector cap.
    tag=[(0,1,(0,)),(0,1,(1,))]
    assert solve(2,tag,(2,),portal_cap=0)[0]=='UNKNOWN'
    assert solve(2,tag,(2,))[0]=='UNSAT'
    print(calls,'original-graph comparisons plus split-clique and separate cap controls passed')
