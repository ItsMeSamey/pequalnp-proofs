"""Exhaustive fixed-instance check, independent of Gaussian elimination."""
from functools import reduce
from operator import xor

E = (34, 13, 40, 46, 57, 31, 19, 30)
P = 3
MASKS = range(1 << len(E))


def subset_sum(mask):
    return reduce(xor, (v for i, v in enumerate(E) if mask >> i & 1), 0)


def attainable(d):
    eligible = sum(1 << i for i, v in enumerate(E) if (d & v).bit_count() % 2 == 0)
    return {subset_sum(m) for m in MASKS if m & ~eligible == 0 and subset_sum(m) < 8}


fibers = [attainable(d) for d in (8, 24, 40, 56)]
assert fibers == [{0}, {0, 1, 4, 5}, {0, 2, 4, 6}, {0, 1, 6, 7}]
relations = [m for m in MASKS if subset_sum(m) == 0]
rep = next(m for m in MASKS if subset_sum(m) == P)
labels = [h for h in MASKS if all(subset_sum(h & m) >> 3 == 0 for m in relations)]
assert all(subset_sum(h & rep) >> 3 != 1 for h in labels)
print("Seven attainable outputs, missing 3. All 256 separator labelings checked.")
