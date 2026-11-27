from itertools import combinations,permutations,product
from random import Random
from strict_forest_reference import circles,swap
from union_band_core import solve
rng=Random(1768)
queries=positives=0
for n in range(1,6):
    triples=[(3*i,3*i+1,3*i+2) for i in range(n)]
    refs=permutations(range(3*n)) if n<=2 else [rng.sample(range(3*n),3*n) for _ in range(50)]
    for ref in refs:
        expected=set()
        for bits in product((0,1),repeat=n):
            p=swap(ref,[(a,(b,c)[x]) for (a,b,c),x in zip(triples,bits)])
            expected.update(pair for tour in circles(p) for pair in combinations(sorted(tour),2))
        pairs=list(combinations(range(3*n),2))
        for a,b in rng.sample(pairs,min(4,len(pairs))):
            result=solve(ref,triples,a,b)
            assert (result is not None)==((a,b) in expected),(ref,a,b)
            queries+=1
            positives+=result is not None
print(queries,positives,queries-positives)
