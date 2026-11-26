from itertools import combinations
from random import Random
rng=Random(522)
def solve(neigh,g,t):
    n=len(neigh); V=set(range(n))
    def gain(S):
        z=0
        for v in S:z^=g[v]
        return z
    def eligible(S):return all(len(neigh[v]&S)%2==0 for v in S)
    def small(U):
        for k in range(min(t,len(U))+1):
            for x in combinations(U,k):yield set(x)
    def subsets(U):
        for k in range(len(U)+1):
            for x in combinations(U,k):yield set(x)
    actual={gain(S) for S in subsets(V) if eligible(S)}
    hits=set()
    for I in small(V):
        if any(neigh[i]&I for i in I):continue
        R=V-I-set().union(*(neigh[i] for i in I))
        H={v for v in R if len(neigh[v]&R)>=3}
        J={v for v in H if neigh[v]&H}
        for P in subsets(J):
            for O in small(H-J):
                selected=P|(H-J-O); live=(R-H)|selected
                # Linear binary edge, vertex parity, and score equations, packed as columns.
                edges=[(u,v) for u in live for v in live&neigh[u] if u<v]
                base=(gain(I)^gain(selected))<<n
                cols=[]
                for u,v in edges:
                    c=(1<<u)|(1<<v)
                    for w in (u,v):
                        if w not in H and len(neigh[w]&live)==2 and min(neigh[w]&live)==(u^v^w):
                            c^=g[w]<<n
                    if u in H and v in H:base^=c
                    else:cols.append(c)
                space={base}
                for c in cols:space|={x^c for x in space}
                hits|={v>>n for v in space if not v&((1<<n)-1)}
    assert hits==actual
for n in range(1,5):
    edges=list(combinations(range(n),2))
    for mask in range(1<<len(edges)):
        N=[set() for _ in range(n)]
        for j,(a,b) in enumerate(edges):
            if mask>>j&1:N[a].add(b);N[b].add(a)
        for t in range(3):solve(N,[rng.randrange(1<<t) for _ in N],t)
for _ in range(100):
    n=rng.randrange(5,9); N=[set() for _ in range(n)]
    for a,b in combinations(range(n),2):
        if rng.random()<0.37:N[a].add(b);N[b].add(a)
    t=rng.randrange(4);solve(N,[rng.randrange(1<<t) for _ in N],t)
print('325 all-target comparisons passed')
