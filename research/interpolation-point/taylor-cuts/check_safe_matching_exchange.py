from itertools import combinations
from random import Random
from safe_matching_exchange import solve


def options(edges,k,V):
    ids=[i for i,(a,b) in enumerate(edges) if V>>a&1 and V>>b&1]
    for w in combinations(ids,k):
        if len({v for i in w for v in edges[i]})==2*k:
            yield w


def affine(n,edges,V,k,P):
    assert all(m.bit_count()<=1 for m in P)
    for w in options(edges,k,V):
        if evaluate(P,w):
            return 'SAT',w
    return 'UNSAT',None


def evaluate(P,w):
    return sum(c for m,c in P.items() if all(i in w for i in range(m.bit_length()) if m>>i&1))%3


if __name__=='__main__':
    rng=Random(244)
    cases=guarded=0
    for j in range(120):
        n=rng.randrange(3,9)
        pairs=list(combinations(range(n),2))
        rng.shuffle(pairs)
        edges=pairs[:rng.randrange(1,min(len(pairs),9)+1)]
        if j%3==0:
            edges.append(edges[0])
        k=rng.randrange(1,min(4,n//2)+1)
        d=2+j%2
        P={}
        for _ in range(12):
            M=sum(1<<i for i in rng.sample(range(len(edges)),rng.randrange(min(d,len(edges))+1)))
            P[M]=rng.randrange(3)
        V=(1<<n)-1
        full=list(options(edges,k,V))
        truth=any(evaluate(P,w) for w in full)
        for opts in ({},{'affine_oracle':affine}):
            status,w,stats=solve(n,edges,k,P,**opts)
            assert status==('SAT' if truth else 'UNSAT')
            if w is not None:
                assert evaluate(P,w) and len({v for i in w for v in edges[i]})==2*k
            cases+=1
        maximum=max(l for l in range(n//2+1) if next(options(edges,l,V),None) is not None)
        if maximum-k>=d-1:
            status,w,stats=solve(n,edges,k,P,brute_cap=0,affine_oracle=affine)
            assert status==('SAT' if truth else 'UNSAT') and stats['brute']==0
            guarded+=1
    # Count selected edges from one C4 with k=1: changing components requires disjoint exchange.
    es=[(u+a,v+a) for a in (0,4) for u,v in ((0,1),(1,2),(2,3),(3,0))]
    P={1<<i:1 for i in range(4)}
    results=[solve(8,es,1,{**P,0:c},brute_cap=0) for c in (0,2)]
    assert all(s=='SAT' for s,w,st in results) and any(st['disjoint']>0 for s,w,st in results)
    # C6 maximum matchings, polynomial cannot be nonzero on any size-3 matching.
    cycle=[(i,(i+1)%6) for i in range(6)]
    impossible={3:1}
    assert solve(6,cycle,3,impossible,brute_cap=0)[0]=='UNKNOWN'
    assert solve(6,cycle,3,impossible)[0]=='UNSAT'
    print(cases,'degree-2/3 oracle comparisons;',guarded,'slack-guarded affine calls; disjoint C4 and tight-cap controls passed')
