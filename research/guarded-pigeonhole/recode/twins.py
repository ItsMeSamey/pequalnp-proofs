"""Differential check of the twin reduction using exhaustive leaf queries."""
from random import Random
from functools import reduce
def labels(cols,x):
    return reduce(int.__xor__,(c for i,c in enumerate(cols) if x>>i&1),0)
def valid(G,x):
    return all(not(x>>i&1) or (row&x).bit_count()%2==0 for i,row in enumerate(G))
def span(gens):
    out={0}
    for d in gens:out|={a^d for a in out}
    return out
if __name__=='__main__':
    r=Random(73991);hits=0;pruned=0
    for trial in range(175):
        k=r.choice((3,4));n=k+r.choice((3,4,5)); C=(1<<k)-1
        nbr=r.randrange(1<<k,1<<n)&~C; G=[0]*n
        for i in range(k):G[i]=nbr
        for j in range(k,n):
            if nbr>>j&1:G[j]|=C
        for i in range(k,n):
            for j in range(i+1,n):
                if r.randrange(2):G[i]|=1<<j;G[j]|=1<<i
        L=[r.randrange(16) for i in range(n)]
        D=span(c^L[0] for c in L[:k])
        if len(D)<4:continue
        raw={labels(L,x) for x in range(1<<n) if valid(G,x)}
        residual={labels(L,x) for x in range(1<<n) if not(x&C) and valid(G,x)}
        branch=set()
        for x in range(1<<n):
            if x&(C^1) or not valid(G,x) or (x&nbr).bit_count()%2:continue
            w=labels(L,x)
            for h in D:
                goal=w^h
                y=next(y for y in range(1<<k) if y.bit_count()%2==(x&1) and labels(L,y)==((L[0] if x&1 else 0)^h))
                u=(x&~C)|y
                assert labels(L,u)==goal and valid(G,u)
                branch.add(goal)
        assert raw==branch|residual
        hits+=16;pruned+=len(raw-branch)
    print(hits,'target comparisons passed,',pruned,'feasible targets required the twins-zero branch')
