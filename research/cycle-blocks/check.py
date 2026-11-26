from random import Random
from itertools import combinations
from solve import solve


def verify(adj, labels, t):
    rows = [sum(1 << v for v in vs) for vs in adj]
    possible = {}
    for x in range(1 << len(adj)):
        if any(x >> i & 1 and (x & row).bit_count() % 2 for i, row in enumerate(rows)):
            continue
        value = 0
        for i, label in enumerate(labels):
            if x >> i & 1:
                value ^= label
        possible[x] = value
    result = solve(adj, labels, t)
    assert result.keys() == set(possible.values())
    assert all(possible[x] == target for target, x in result.items())


rng = Random(71483)
for n in range(5):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        adj = [[] for _ in range(n)]
        for i, (u, v) in enumerate(pairs):
            if mask >> i & 1:
                adj[u].append(v)
                adj[v].append(u)
        for t in range(4):
            verify(adj, [rng.randrange(1 << t) for _ in adj], t)
for _ in range(400):
    n = rng.randrange(2, 10)
    adj = [[] for _ in range(n)]
    for u, v in combinations(range(n), 2):
        if rng.randrange(4) == 0:
            adj[u].append(v)
            adj[v].append(u)
    t = rng.randrange(1, 5)
    verify(adj, [rng.randrange(1 << t) for _ in adj], t)
print("Checked all 76 graphs through four vertices at four marker widths and 400 further graphs.")
