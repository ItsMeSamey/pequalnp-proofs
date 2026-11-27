from itertools import combinations
from random import Random
from collections import Counter
from solver import solve
counts=Counter()
def test(n,edges,q,B,W,J,requests,mode):
    m=len(edges); a=len(W); h=len(q)
    sig=[sum((v in e)<<i for i,v in enumerate(q)) for e in edges]
    N=m+a; adj=[0]*N
    for i,j in combinations(range(N),2):
        if j<m:
            toggle=sum(((sig[i]>>l)&1)*((sig[j]&B[l]).bit_count()%2) for l in range(h))%2
            bit=bool(set(edges[i])&set(edges[j]))^bool(toggle)
        elif i<m:bit=(sig[i]&W[j-m]).bit_count()%2
        else:bit=J[i-m]>>(j-m)&1
        if bit:adj[i]|=1<<j; adj[j]|=1<<i
    good={s for s in range(1<<N) if all(not(s>>i&1) or (s&row).bit_count()%2==0 for i,row in enumerate(adj))}
    for pins in requests:
        need=sum(1<<i for i in pins)
        ans=solve(n,edges,q,B,W,J,pins)
        exp=any(s&need==need for s in good)
        assert (ans is not None)==exp,(n,edges,q,B,W,J,pins,ans)
        if ans is not None:
            actual=sum(1<<i for i in ans)
            assert actual in good and actual&need==need
        counts[mode,exp]+=1
for mask in range(8):
    edges=[e for i,e in enumerate(combinations(range(3),2)) if mask>>i&1]
    for b in range(8):
        B=[(b&1)|((b>>1&1)<<1), (b>>1&1)|((b>>2&1)<<1)]
        for w in range(4):
            N=len(edges)+1
            test(3,edges,[0,1],B,[w],[0],
                 [ps for j in range(N+1) for ps in combinations(range(N),j)],'exhaustive')
r=Random(9922)
for _ in range(600):
    n=r.randrange(3,9); universe=list(combinations(range(n),2)); edges=r.sample(universe,r.randrange(1,min(10,len(universe))+1))
    h=r.randrange(1,min(n,4)+1); q=r.sample(range(n),h); B=[0]*h
    for i in range(h):
        for j in range(i,h):
            if r.randrange(2):B[i]|=1<<j;B[j]|=1<<i
    a=r.randrange(4); W=[r.randrange(1<<h) for i in range(a)]; J=[0]*a
    for i,j in combinations(range(a),2):
        if r.randrange(2):J[i]|=1<<j;J[j]|=1<<i
    N=len(edges)+a
    test(n,edges,q,B,W,J,[r.sample(range(N),r.randrange(min(6,N)+1))],'sample')
print(counts)
