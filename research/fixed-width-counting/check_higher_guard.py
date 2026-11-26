from itertools import combinations
from random import Random

def check(n, clauses, pools, d):
    end = 1 << n
    def violates(x, clause):
        mask, pattern = clause
        return x & mask == pattern
    blocked = {a for a in range(1, end) if sum(a & b == a for b in pools) >= d}
    oracle = sum(all(a & b != a or not violates(x, c) for b, c in zip(pools, clauses))
                 for x in range(end) for a in range(end) if a not in blocked)
    source = sum(all(not violates(x, c) for c in clauses) for x in range(end))
    contamination = (end-1-len(blocked))*end
    for j in range(1, min(d, len(clauses)+1)):
        for batch in combinations(range(len(clauses)), j):
            common = end-1
            for i in batch:
                common &= pools[i]
            allowed = 2**common.bit_count()-1-sum(a & common == a for a in blocked)
            assignments = sum(all(violates(x, clauses[i]) for i in batch) for x in range(end))
            contamination += (-1)**j * allowed * assignments
    assert oracle-contamination == source

rng = Random(109)
for case in range(650):
    n = rng.randrange(1,7)
    clauses = []
    pools = []
    for _ in range(rng.randrange(9)):
        mask = rng.randrange(1<<n)
        clauses.append((mask,mask & rng.randrange(1<<n)))
        pools.append(sum(1<<i for i in rng.sample(range(n),mask.bit_count())))
    check(n,clauses,pools,rng.randrange(2,7))
print("650 exact guard oracle checks passed")
