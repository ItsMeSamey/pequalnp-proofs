"""Finite simple cores for the three-part sum lemma; no dependencies."""
from itertools import combinations
from functools import reduce
from operator import xor


def can_partition(types):
    states = {(0, 0)}
    for v in types:
        states = states | {(a ^ v, b) for a, b in states} | {(a, b ^ v) for a, b in states}
        if (1, 2) in states:
            return True
    return False


for r in (2, 3, 4):
    checked = failed = unsupported = 0
    for size in range((1 << r)):
        for types in combinations(range(1, 1 << r), size):
            if reduce(xor, types, 0) != 0:
                continue
            weights = [sum((v & f).bit_count() % 2 for v in types) for f in range(1, 1 << r)]
            if 0 in weights:
                continue
            checked += 1
            if not can_partition(types):
                failed += 1
                if not any(weights[f - 1] == 2 for f in range(4, 1 << r, 4)):
                    unsupported += 1
                    assert r == 3 and types == (4, 5, 6, 7), (r, types)
    print(r, checked, failed, unsupported)
