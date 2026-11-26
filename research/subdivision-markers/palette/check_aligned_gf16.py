"""Check literal GF(16) column ranks against binary common-cocircuit tests."""
from itertools import combinations
from random import Random


def mul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 16:
            a ^= 0b10011  # t^4+t+1
    return out


def field_rank(columns):
    pivots = {}
    for col in columns:
        v = list(col)
        for i in range(len(v)):
            if not v[i]:
                continue
            if i not in pivots:
                inv = next(b for b in range(1, 16) if mul(v[i], b) == 1)
                pivots[i] = [mul(x, inv) for x in v]
                break
            v = [x ^ mul(v[i], y) for x, y in zip(v, pivots[i])]
    return len(pivots)


def coords(v, r):
    return tuple((v >> i) & 1 for i in range(r))


def trial(E, a, g):
    r = len(g)
    C = [coords(e, r) for e in E]
    different = any(field_rank((*S, coords(a, r))) == r and
                    field_rank((*S, g)) < r for S in combinations(C, r-1))
    slices = [sum(((v >> j) & 1) << i for i, v in enumerate(g)) for j in range(4)]
    # Keeping redundant slices gives equivalent hyperplane constraints.
    probes = [a] + [a ^ v for v in slices]
    common = False
    for f in range(1, 1 << r):
        if all((f & v).bit_count() % 2 for v in probes):
            flat = [c for c, e in zip(C, E) if (f & e).bit_count() % 2 == 0]
            if field_rank(flat) == r-1:
                common = True
                break
    assert common == different


rng = Random(43517)
count = 0
for r in (2, 3, 4, 5):
    for j in range(150):
        E = [1 << i for i in range(r)] + [rng.randrange(1 << r) for _ in range(3)]
        a = rng.randrange(1 << r)
        g = [rng.randrange(1 << (j % 5)) for _ in range(r)]
        trial(E, a, g)
        count += 1
print(f'{count} literal GF(16) rank comparisons passed')
