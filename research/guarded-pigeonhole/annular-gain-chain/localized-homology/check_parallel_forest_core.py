from itertools import combinations, product
from random import Random
from parallel_forest_core import solve
from strict_forest_reference import circles, swap

rng = Random(1767)
queries = yes = no = 0
for n in range(1,8):
    triples = [(3*i,3*i+1,3*i+2) for i in range(n)]
    for _ in range(60):
        slots = [[] for _ in range(rng.randrange(1,2*n+1))]
        for a,b,c in triples:
            rng.choice(slots).append(a)
            rng.choice(slots).extend([b,c])
        ref = [None]*(3*n)
        for row in slots:
            rng.shuffle(row)
            for a,b in zip(row,row[1:]+row[:1]):
                ref[a]=b
        expected = set()
        for xs in product((0,1),repeat=n):
            tours = circles(swap(ref,[(a,(b,c)[x]) for (a,b,c),x in zip(triples,xs)]))
            expected.update(pair for tour in tours for pair in combinations(sorted(tour),2))
        pairs = list(combinations(range(3*n),2))
        for a,b in rng.sample(pairs,min(len(pairs),9)):
            found,bits = solve(ref,triples,a,b)
            assert found and ((bits is not None)==((a,b) in expected))
            queries+=1
            yes+=bits is not None
            no+=bits is None
print(queries,yes,no)
