from random import Random
from subdivision import search

rng=Random(302)
for trial in range(2000):
    n=rng.randrange(3,11)
    A=[set() for _ in range(n)]
    def edge(i,j):
        A[i].add(j)
        A[j].add(i)
    for i in range(n):
        edge(i,(i+1)%n)
    for i in range(n):
        for j in range(i):
            if rng.random()<0.2:
                edge(i,j)
    # Arbitrary nonuniform edge subdivisions preserve biconnectivity.
    edges=[(i,j) for i in range(n) for j in A[i] if i<j]
    for i,j in rng.sample(edges,rng.randrange(min(len(edges),13-n)+1)):
        h=len(A)
        A.append(set())
        A[i].remove(j)
        A[j].remove(i)
        edge(i,h)
        edge(h,j)
    s=rng.randrange(len(A))
    t=rng.choice(sorted(A[s]))
    marked={i for i in range(len(A)) if rng.randrange(2)}
    reachable=set()
    rest=[i for i in range(len(A)) if i not in (s,t)]
    for bits in range(1<<len(rest)):
        X={s,t}|{v for i,v in enumerate(rest) if bits>>i&1}
        if all(len(A[v]&X)%2==0 for v in X):
            reachable.add(len(marked&X)%2)
    for target in (0,1):
        result=search(A,s,t,marked,target)
        assert (result is not None)==(target in reachable)
        if result is not None:
            assert {s,t}<=result and len(marked&result)%2==target
            assert all(len(A[v]&result)%2==0 for v in result)
print('4000 weighted decisions checked')
