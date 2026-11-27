"""Exact full-graph ternary profile and every edge pin at m=1."""
from collections import Counter
from functools import cache
from itertools import combinations

m = 1
pool_width = m + 2
n_principals = 3 * pool_width
n = n_principals + 9 * m
edges = {}
for u, v in combinations(range(n), 2):
    if v < n_principals:
        edges[u, v] = (u // pool_width) * (v // pool_width) % 3
    elif u < n_principals:
        group = u // pool_width
        if group == (v - n_principals) // (3 * m):
            edges[u, v] = 2 * group**2 % 3
    elif (u - n_principals) // 3 == (v - n_principals) // 3:
        edges[u, v] = 0

@cache
def profile(mask):
    if mask == 0:
        return (1, 0, 0)
    v = mask.bit_length() - 1
    answer = [0, 0, 0]
    for u in range(v):
        if mask >> u & 1 and (u, v) in edges:
            gain = edges[u, v]
            for h, count in enumerate(profile(mask ^ (1 << u) ^ (1 << v))):
                answer[(gain + h) % 3] += count
    return tuple(answer)

full = (1 << n) - 1
counts = profile(full)
pins = Counter()
for (u, v), g in edges.items():
    residual = profile(full ^ (1 << u) ^ (1 << v))
    included = tuple(residual[(i-g)%3] for i in range(3))
    excluded = tuple(total-part for total,part in zip(counts,included))
    for case in included, excluded:
        assert {i for i,c in enumerate(case) if c} == {0,2}
    pins['principal' if v < n_principals else 'external' if u < n_principals else 'internal'] += 1
print(n, counts, dict(pins))
