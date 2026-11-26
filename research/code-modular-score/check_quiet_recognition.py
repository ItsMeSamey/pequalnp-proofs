"""Cross-check recursive quiet recognition against original cycle enumeration."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from random import Random

rng = Random(14273)
stats = Counter()


def span(values):
    space = {0}
    for v in values:
        space |= {x ^ v for x in space}
    return space


def check(edges, n, mod, k):
    m = len(edges)
    vertex_columns = [(1 << u) ^ (1 << v) for u, v, _ in edges]
    cycles = [0]
    boundaries = {0: 0}
    basis = []
    for i, col in enumerate(vertex_columns):
        if col in boundaries:
            basis.append((1 << i) ^ boundaries[col])
        else:
            boundaries.update({v ^ col: x ^ (1 << i) for v, x in list(boundaries.items())})
    cycles = span(basis)
    nonzero = [x for x in cycles if sum(w for i, (_, _, w) in enumerate(edges) if x >> i & 1) % mod]
    forms = [sum(1 << j for j, b in enumerate(basis) if b >> i & 1) for i in range(m)]
    subsets = [s for l in range(min(k,m)+1) for s in combinations(range(m), l)]
    expected = any(all(any(x >> i & 1 for i in s) for x in nonzero) for s in subsets)

    @lru_cache(None)
    def solve(W):
        sums = Counter()
        for (_, _, w), a in zip(edges, forms):
            sums[min(a ^ z for z in W)] += w
        A = {a for a, total in sums.items() if a and total % mod}
        if not A:
            stats['leaves'] += 1
            for s in subsets:
                surviving = [x for x in cycles if not any(x >> i & 1 for i in s)]
                # Test the leaf by explicit row labels on cycle-basis combinations.
                live = {0: 0}
                for j, b in enumerate(basis):
                    live.update({x ^ b: z ^ (1 << j) for x,z in list(live.items())})
                if all(not ((live[x] & w).bit_count() & 1) for x in surviving for w in W):
                    return True
            return False
        if len(W) >= 1 << k:
            return False
        if len(A) <= 1 << (k+1):
            shifts = A | {a ^ b for a,b in combinations(A,2)}
        else:
            stats['heavy'] += 1
            shifts = {h for h in {a^b for a,b in combinations(A,2)}
                      if len(A.intersection(a^h for a in A)) * (1 << (k+1)) >= len(A)}
        return any(solve(frozenset(set(W) | {z ^ h for z in W})) for h in shifts)

    result = solve(frozenset({0}))
    assert result == expected, (edges,mod,k)
    stats['cases'] += 1


for _ in range(500):
    n = rng.randrange(2,8)
    mod = rng.choice([3,5,9,15])
    edges = [(rng.randrange(n),rng.randrange(n),rng.randrange(mod)) for _ in range(rng.randrange(2,11))]
    check(edges,n,mod,rng.randrange(3))
print(dict(stats))
