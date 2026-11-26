from itertools import combinations
from random import Random
def check(n, pairs):
    m=len(pairs)
    N=2*n+m+1
    hub=n
    rows=[0]*N
    def edge(i,j):
        rows[i]|=1<<j
        rows[j]|=1<<i
    for j,(s,t) in enumerate(pairs):
        i=n+1+j
        edge(i,s)
        edge(i,t)
    for i in range(n):
        z=n+1+m+i
        edge(z,i)
        edge(z,hub)
    expected=sum(1<<sum(((x>>u)&1)==((x>>v)&1) for u,v in pairs)
                 for x in range(1<<n))
    actual=sum(all(not (s>>i&1) or (row&s).bit_count()%2==0 for i,row in enumerate(rows))
               for s in range(1<<N) if s>>hub&1)
    assert actual==expected
rng=Random(6915)
for n in range(2,5):
    E=list(combinations(range(n),2))
    for _ in range(65):
        check(n,[rng.choice(E) for j in range(rng.randrange(5))])
print('195 symmetric bipartite hub-gadget counts passed.')
