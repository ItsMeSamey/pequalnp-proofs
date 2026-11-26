"""Independent finite checks of the cone counting and residual expansion estimates."""
import itertools
import random

rng = random.Random(401399)
for _ in range(500):
    depth = rng.randrange(4,10)
    protected = rng.randrange(1,depth)
    removed = set(rng.sample(range(2**(protected+1), 2**(depth+1)), rng.randrange(2**protected)))
    reached = 0
    for leaf in range(2**depth, 2**(depth+1)):
        ancestor = leaf
        while ancestor and ancestor not in removed:
            ancestor //= 2
        reached += not ancestor
    assert reached >= 2**depth-len(removed)*2**(depth-protected)
cases=0
for _ in range(180):
    n=rng.randint(5,10)
    edges=[{j for j in range(n) if j!=i and rng.random()<.4} for i in range(n)]
    for i in range(n):
        for j in list(edges[i]): edges[j].add(i)
    def neighbours(S):
        return set().union(*(edges[i] for i in S))-S
    alpha=min(1,min(len(neighbours(set(X)))/len(X) for k in range(1,n//2+1) for X in itertools.combinations(range(n),k)))
    if alpha==0: continue
    for k in range(1,n//2+1):
        for X in itertools.combinations(range(n),k):
            X=set(X)
            F=set(rng.sample(sorted(set(range(n))-X),rng.randrange(3)))
            if alpha*len(X)>2*len(F):
                assert len(neighbours(X)-F)>=alpha*len(X)/2
                cases+=1
print(f"500 protected trees and {cases} residual growth steps checked")
