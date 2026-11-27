from itertools import combinations
from random import Random
from exact_line import exact_line


def direct(columns, pins):
    optional = sorted(set(range(len(columns))) - set(pins))
    for size in range(len(optional) + 1):
        for extra in combinations(optional, size):
            span = {0}
            for i in (*pins, *extra):
                span |= {x ^ columns[i] for x in span}
            if span & set(range(8)) == {0, 1}:
                return True
    return False


def check(columns, pins):
    witness = exact_line(columns, 1, 2, 4, forced=pins)
    assert (witness is not None) == direct(columns, pins), (columns, pins, witness)
    if witness is not None:
        assert set(pins) <= set(witness)
        span = {0}
        for i in witness:
            span |= {v ^ columns[i] for v in span}
        assert span & set(range(8)) == {0, 1}


if __name__ == "__main__":
    rng = Random(32768)
    for mask in range(128):
        cols = [i + 1 for i in range(7) if mask >> i & 1]
        check(cols, ())
    for i in range(80):
        n = rng.randrange(3, 9)
        r = rng.randrange(3, 6)
        cols = [rng.randrange(1 << r) for _ in range(n)]
        check(cols, ())
        check(cols, tuple(j for j in range(n) if rng.randrange(3) == 0))
    print("128 exhaustive + 160 seeded decisions and witnesses passed")
