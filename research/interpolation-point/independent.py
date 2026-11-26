"""Replay the two-selector construction by summing physical hub choices."""

from itertools import combinations, product
from math import prod
from random import Random

rng = Random(20261126)


def hub(alpha, beta, gamma):
    # Choice 0 is idle. The interhub term selects neither external leg.
    result = {0: gamma}
    for left, right in product(range(len(alpha)), repeat=2):
        if left == right and left:
            continue
        mask = sum(1 << (i - 1) for i in (left, right) if i)
        result[mask] = result.get(mask, 0) + alpha[left] * beta[right]
    return result


def augmented_rank(weights, degree):
    rows = [0] * (degree + 1)
    for i, j in combinations(range(degree + 1), 2):
        mask = (1 << (j - 1)) | ((1 << (i - 1)) if i else 0)
        if weights.get(mask, 0) % 2:
            rows[i] |= 1 << j
            rows[j] |= 1 << i
    pivots = {}
    for row in rows:
        while row:
            col = row.bit_length() - 1
            if col not in pivots:
                pivots[col] = row
                break
            row ^= pivots[col]
    return len(pivots)


def interface(left, right, edges):
    return sum(a * b * prod(w[(s >> i & 1) * 2 + (t >> i & 1)]
                            for i, w in enumerate(edges))
               for s, a in left.items() for t, b in right.items())


def rank_two_lift(weights, degree):
    for alpha, beta in product(product(range(2), repeat=degree + 1), repeat=2):
        candidate = hub(alpha, beta, weights[0] - alpha[0] * beta[0])
        if all((weights[s] - value) % 2 == 0 for s, value in candidate.items()):
            return candidate
    raise ValueError("no two-selector lift")


def scale_vertex(weights):
    return {s: a << (2 - s.bit_count()) for s, a in weights.items()}


rank_four = {3: 1, 12: 1}
star = {3: 1, 5: 1, 9: 1}
assert augmented_rank(rank_four, 4) == 4
assert augmented_rank(star, 4) == 2

for trial in range(32):
    d = 4
    alpha = [rng.randrange(-4, 5) for _ in range(d + 1)]
    beta = [rng.randrange(-4, 5) for _ in range(d + 1)]
    gamma = rng.randrange(-7, 8)
    out = hub(alpha, beta, gamma)
    assert out[0] == alpha[0]*beta[0] + gamma
    for i in range(1, d+1):
        assert out[1 << (i-1)] == alpha[i]*beta[0] + beta[i]*alpha[0]
    for i, j in combinations(range(1, d+1), 2):
        assert out[(1 << (i-1)) | (1 << (j-1))] == alpha[i]*beta[j] + beta[i]*alpha[j]
    assert augmented_rank(out, d) <= 2

# Five parallel edges give H=5-2*2=1. Use star pair weights mod 2.
# Brute-force search for each lift avoids reusing the pivot construction.
d = 5
masks = [s for s in range(1 << d) if s.bit_count() <= 2]
for trial in range(24):
    weights = [{s: 2*rng.randrange(8) + (rng.randrange(2) if s.bit_count()<2 else
                int(bool(s & (1 << center)))) for s in masks} for center in (0, 1)]
    edges = [[2*rng.randrange(8)] + [rng.randrange(16) for _ in range(3)] for i in range(d)]
    scaled = [scale_vertex(w) for w in weights]
    lifted = [rank_two_lift(w, d) for w in scaled]
    defects = [{s: w[s]-b[s] for s in masks} for w, b in zip(scaled, lifted)]
    transformed = [[a//2, b, c, 2*e] for a,b,c,e in edges]
    raw = interface(*weights, edges)
    assert raw == 2 * interface(*scaled, transformed)
    for k in (1, 2, 3, 4):
        total = 0
        for i,j in product(range(2), repeat=2):
            if i+j < k:
                total += interface((lifted,defects)[i][0], (lifted,defects)[j][1], transformed)
        assert (raw - 2*total) % (1 << (k+1)) == 0

print("32 integer hub checks; augmented rank 4 rejected, star rank 2; 24 scale identities and 96 precision/defect comparisons passed")
