"""Compare all targets with brute-force vertex subsets on exhaustive and seeded graphs."""
from itertools import combinations, product
from random import Random
from solver import solve

def check(rows, labels, t):
    n = len(rows)
    expected = set()
    def inspect(mask):
        value = 0
        for i in range(n):
            if mask >> i & 1:
                if sum(mask >> j & 1 for j in rows[i]) % 2:
                    return None
                value ^= labels[i]
        return value
    for s in range(1 << n):
        expected.add(inspect(s))
    for z in range(1 << t):
        s = solve(rows, labels, z, t)
        assert (s is not None) == (z in expected)
        assert s is None or inspect(s) == z
    return 1 << t

if __name__ == '__main__':
    count = 0
    for n in range(4):
        edges = list(combinations(range(n), 2))
        for bits in range(1 << len(edges)):
            rows = [[] for _ in range(n)]
            for k,(a,b) in enumerate(edges):
                if bits >> k & 1:
                    rows[a].append(b)
                    rows[b].append(a)
            for labels in product(range(4), repeat=n):
                count += check(rows, labels, 2)
    print('exhaustive', count, flush=True)
    rng = Random(318671)
    count = 0
    for k in range(300):
        core = rng.randrange(2,8)
        rows = [[] for _ in range(core)]
        for a,b in combinations(range(core), 2):
            if len(rows) < 14 and rng.randrange(3) == 0:
                c = len(rows)
                rows.append([a,b])
                rows[a].append(c)
                rows[b].append(c)
        t = rng.randrange(5)
        count += check(rows, [rng.randrange(1 << t) for _ in rows], t)
    print('seeded', count)
