from itertools import combinations
from random import Random
from solve import triangle_minor


def dot(x, y):
    return (x & y).bit_count() % 2


def states(cols, dimension, contracted=(), kept=None):
    if kept is None:
        kept = range(len(cols))
    # A cycle lift may use contracted columns, while a covector annihilates them.
    sums = {0}
    for j in contracted:
        sums |= {s ^ cols[j] for s in sums}
    result = set()
    for f in range(1 << dimension):
        if any(dot(f, cols[j]) for j in contracted):
            continue
        available_sums = sums.copy()
        for j in kept:
            if not dot(f, cols[j]):
                available_sums |= {s ^ cols[j] for s in available_sums}
        result.update((s, f & 3) for s in available_sums if s < 4)
    return result


def check(cols, dimension):
    kind, contracted, kept = triangle_minor(cols)
    assert len(kept) <= 3
    assert states(cols, dimension) == states(cols, dimension, contracted, kept)
    return kind


rng = Random(7541)
counts = {'parallel': 0, 'star': 0}
for size in range(6):
    for cols in combinations(range(16), size):
        counts[check(cols, 4)] += 1
for _ in range(600):
    dim = rng.randrange(2, 8)
    cols = [rng.randrange(1 << dim) for _ in range(rng.randrange(13))]
    counts[check(cols, dim)] += 1
print(counts)
