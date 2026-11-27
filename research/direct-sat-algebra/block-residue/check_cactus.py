"""Bounded raw-assignment oracle for signed cactus-copy shells."""
from itertools import combinations_with_replacement, product
from random import Random

from cactus_copy import NonCactusError, cactus_witness


def valid(raw, shells, pins):
    return all(raw[a] ^ raw[b] == s for a, b, s in pins) and all(
        raw[i:i+2] != raw[i+2:i+4] for i in range(0, 4 * shells, 4)
    )


def compare(shells, pins, allow_outside=False):
    try:
        result = cactus_witness(shells, pins)
    except NonCactusError:
        if allow_outside:
            return
        raise
    exists = any(valid(x, shells, pins) for x in product((0, 1), repeat=4*shells))
    assert (result is not None) == exists, (shells, pins, result)
    if result is not None:
        assert valid(result, shells, pins)


def check():
    compare(0, [])
    options = [(a, b, s) for a in range(4) for b in range(a, 4) for s in (0, 1)]
    for k in range(4):
        for pins in combinations_with_replacement(options, k):
            compare(1, pins)
    # Two violated cycles: the singleton loop requires shell 1;
    # the two-comparison cycle must move its repair to shell 0.
    compare(2, [(0, 4, 0), (2, 6, 1), (5, 7, 0)])
    # Two unsigned loops competing for the same shell.
    compare(1, [(0, 2, 0), (1, 3, 0)])
    # Three parallel comparisons produce overlapping two-edge cycles.
    try:
        cactus_witness(2, [(0, 1, 0), (0, 4, 0), (2, 3, 0), (2, 6, 0)])
    except NonCactusError:
        pass
    else:
        raise AssertionError("expected noncactus")
    rng = Random(404)
    for _ in range(150):
        pins = [(rng.randrange(8), rng.randrange(8), rng.randrange(2))
                for _ in range(rng.randrange(11))]
        compare(2, pins, allow_outside=True)
    print("signed cactus-copy oracle passed")


if __name__ == "__main__":
    check()
