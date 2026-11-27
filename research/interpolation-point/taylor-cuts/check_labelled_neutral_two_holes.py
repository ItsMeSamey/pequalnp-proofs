from itertools import combinations
from random import Random
from labelled_neutral_two_holes import solve

def exhaustive(V,edges):
    if not V:
        yield (0,())
        return
    u=min(V)
    for i,(v,w,g) in enumerate(edges):
        if v in V and w in V and u in (v,w):
            for h,tr in exhaustive(V-{v,w},edges):
                yield ((h+g[0])%3,(i,)+tr)

if __name__=='__main__':
    rng=Random(7145)
    comparisons=0
    nontrivial=False
    for j in range(42):
        n=2*rng.randrange(1,5)
        V=set(range(n))
        edges=[(u,v,(0,)) for u,v in combinations(range(n),2)
               if (u//2==v//2 or rng.randrange(4)==0)]
        allowed={i for _,tr in exhaustive(V,edges) for i in tr}
        potential=[rng.randrange(3) for _ in V]
        edges=[(u,v,((potential[u]+potential[v]+(rng.randrange(3) if i not in allowed else 0))%3,))
               for i,(u,v,_) in enumerate(edges)]
        for h in rng.sample(list(combinations(range(n),2)),min(4,n*(n-1)//2)):
            expected={g for g,_ in exhaustive(V-set(h),edges)}
            nontrivial |= len(expected)>1
            for g in range(3):
                status,tr,_=solve(n,edges,h,(g,),audit_neutral=True)
                assert status==('SAT' if g in expected else 'UNSAT'),(edges,h,g)
                comparisons+=1
    assert nontrivial
    assert solve(2,[(0,1,(0,))],(0,1),(0,),state_cap=0)[0]=='UNKNOWN'
    assert solve(2,[],(0,1),(0,))[0]=='UNKNOWN'
    try:
        solve(2,[(0,1,(0,)),(0,1,(1,))],(0,1),(0,),audit_neutral=True)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid promise accepted')
    print(comparisons,'neutral original-edge hole targets plus cap and promise controls passed')
