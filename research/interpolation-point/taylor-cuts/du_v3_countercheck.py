"""Exhaustive checks on the two fixed review examples only."""
from itertools import combinations

edges = [(i, (i + 1) % 6) for i in range(6)]
red_ids = {0, 4}
matchings = [ids for ids in combinations(range(6), 3)
             if len({v for i in ids for v in edges[i]}) == 6]
assert matchings == [(0, 2, 4), (1, 3, 5)]
crossings = {2, 5}
assert all(len(set(ids) & crossings) == 1 for ids in matchings)
actual = {len(set(ids) & red_ids) for ids in matchings}
local = [{int(red in ids) for ids in matchings} for red in sorted(red_ids)]
independent = {a + b for a in local[0] for b in local[1]}
assert actual == {0, 2} and independent == {0, 1, 2}

def cofactor_terms(lam):
    a, b = lam, lam + 2
    return a * b**3, a**3 * b

for lam in range(-3, 4):
    left, right = cofactor_terms(lam)
    assert left - right == 4 * lam * (lam + 1) * (lam + 2)
assert cofactor_terms(-1) == (-1, -1)
assert (3 - 2) * (5 - 2) * (5 - 3) == 6
print("C6 yields {0,2}; independent blocks yield {0,1,2}.")
print("At lambda=-1 both cofactor terms equal -1; their difference is zero.")
