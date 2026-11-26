from itertools import combinations
from random import Random
from solver import (LinearBasis, backdoor, coordinate_basis, obstruction,
                    normalized_forbidden, parity, solve)


def legal(x, guards, markers):
    return all(parity(x & m) == c for m, c in markers) and all(
        not ((parity(x & a) ^ c) and (parity(x & b) ^ d)) for a, c, b, d in guards)


def check(n, guards, markers):
    x, size = solve(n, guards, markers)
    assert (x is not None) == any(legal(i, guards, markers) for i in range(1 << n))
    assert x is None or legal(x, guards, markers)
    return size


rng = Random(61297)
for _ in range(1500):
    n = rng.randrange(9)
    gs = [(rng.getrandbits(n), rng.randrange(2), rng.getrandbits(n), rng.randrange(2))
          for i in range(rng.randrange(13))]
    ms = [(rng.getrandbits(n), rng.randrange(2)) for i in range(rng.randrange(5))]
    check(n, gs, ms)

for _ in range(400):
    dim = rng.randrange(1, 5)
    flats = [normalized_forbidden([(rng.getrandbits(dim), 0) for j in range(2)])
             for i in range(rng.randrange(10))]
    sets = [{m for m, _ in flat} for flat in flats]
    for S in sets:
        if len(S) == 2:
            a, b = S
            S.add(a ^ b)
    def score(basis):
        return sum(len(set(basis) & S) for S in sets)
    best = 0
    for cand in combinations(range(1, 1 << dim), dim):
        bb = LinearBasis()
        for c in cand:
            bb.add(c)
        if len(bb.normals) == dim:
            best = max(best, score(cand))
    chosen = coordinate_basis(flats, dim)
    assert score(chosen.normals) == best
    rew = [tuple((chosen.reduce(m)[1], b) for m, b in flat) for flat in flats]
    def is_good(mask):
        for flat in rew:
            support = 0
            remaining = LinearBasis()
            for m, _ in flat:
                support |= m & ~mask
                remaining.add(m & ~mask)
            if support.bit_count() != len(remaining.normals):
                return False
        return True
    for mask in range(1 << dim):
        assert (not obstruction(rew, mask)) == is_good(mask)
    assert backdoor(rew).bit_count() == min(m.bit_count() for m in range(1 << dim) if is_good(m))

for _ in range(200):
    n = rng.randrange(2, 9)
    basis = LinearBasis()
    while len(basis.normals) < n:
        basis.add(rng.getrandbits(n))
    gs = []
    for i, j in combinations(range(n), 2):
        if rng.randrange(2):
            a, b = basis.normals[i], basis.normals[j]
            # Forbidden point of this plane; neither presented row need be the desired coordinate pair.
            gs.append((a ^ b, rng.randrange(2), b, rng.randrange(2)))
    assert check(n, gs, []) == 0

for n in (8, 16, 32):
    # Native acyclic guard, one per paired edge. Polar rank n, coordinate backdoor zero.
    gs = [(1 << (i + 1), 0, 1 << i, 0) for i in range(0, n, 2)]
    x, s = solve(n, gs, [(1, 1)])
    assert s == 0 and legal(x, gs, [(1, 1)])
print("1,500 general slices, 400 basis/backdoor audits, 200 hidden-coordinate graphs, 3 rank separations passed")
