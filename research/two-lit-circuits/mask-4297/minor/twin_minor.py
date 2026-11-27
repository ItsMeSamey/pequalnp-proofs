"""Exhaust a single-fork circuit by decomposing its two read-once trees."""
from functools import cache
from itertools import combinations, product

rows = [s for s in range(16) if s.bit_count() in (1, 2)]
full = (1 << len(rows)) - 1
raw = [sum(1 << i for i, s in enumerate(rows) if s >> j & 1) for j in range(4)]
target = sum(1 << i for i, s in enumerate(rows) if s in (1, 2, 5))

@cache
def trees(leaves, neg):
    if len(leaves) == 1:
        return {leaves[0] ^ (full if neg else 0)}
    out = set()
    if neg:
        out.update(x ^ full for x in trees(leaves, 0))
    for mask in range(1, (1 << len(leaves))-1, 2):
        a = tuple(x for i,x in enumerate(leaves) if mask >> i & 1)
        b = tuple(x for i,x in enumerate(leaves) if not(mask >> i & 1))
        for k in range(neg+1):
            for u,v in product(trees(a,k),trees(b,neg-k)):
                out.update((u & v,u | v))
    return out

seen = set()
for k in range(4):
    for rest in combinations(range(1,4), k):
        shared = (0,) + rest
        outside = tuple(raw[i] for i in range(4) if i not in shared)
        for h in trees(tuple(raw[i] for i in shared), 0):
            seen.update(trees(tuple(sorted((*outside,h,h))),1))
print(len(seen), target in seen)
assert target not in seen
