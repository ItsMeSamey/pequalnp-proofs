"""Finite checks of collision truncation and the explicit grid promise control."""
from collections import Counter
from itertools import combinations, product
from random import Random


def add(poly, key, value):
    poly[key] += value
    if not poly[key]:
        del poly[key]


def delta(poly, i):
    answer = Counter()
    for exps, c in poly.items():
        if exps[i] > 1:
            key = list(exps)
            key[i] = 1
            add(answer, tuple(key), c)
            add(answer, exps, -c)
    return answer


def correct(poly, h, variables):
    out = Counter()
    for j in range(h + 1):
        for chosen in combinations(range(variables), j):
            term = poly
            for i in chosen:
                term = delta(term, i)
            for key, c in term.items():
                add(out, key, c)
    return {key: c for key, c in out.items() if sum(key) == 3}


def check_collisions():
    # Two directed 3-cycles, in the six arc coordinates.
    base = {(1, 1, 1, 0, 0, 0): 1, (0, 0, 0, 1, 1, 1): 1}
    rng = Random(93741)
    for h in range(1, 4):
        for _ in range(16):
            poly = Counter(base)
            for _ in range(12):
                n = rng.randrange(1, 7)
                support = rng.sample(range(6), n)
                key = tuple(int(i in support) for i in range(6))
                powers = list(key)
                for i in rng.sample(support, rng.randrange(1 + (min(h, n) if n <= 3 else n))):
                    powers[i] += rng.randrange(1, 5)
                add(poly, tuple(powers), 1)
                add(poly, key, -1)
            assert correct(poly, h, 6) == base
    poly = Counter(base)
    old = (1, 1, 1, 0, 0, 0)
    del poly[old]
    poly[(2, 2, 2, 0, 0, 0)] = 1
    assert correct(poly, 2, 6) != base and correct(poly, 3, 6) == base


def gf2_rank(rows):
    pivots = {}
    for v in rows:
        while v:
            k = v.bit_length() - 1
            if k not in pivots:
                pivots[k] = v
                break
            v ^= pivots[k]
    return len(pivots)


def check_grid():
    # A 2x2 grid is a cycle. A tuple at i gives its incoming and outgoing bit.
    states = tuple(product(range(2), repeat=2))
    for config in product((None,) + states, repeat=4):
        expected = all(s is not None for s in config) and all(
            config[i][1] == config[(i + 1) % 4][0] for i in range(4))
        value = 1
        for i in range(4):
            left, right = config[i], config[(i + 1) % 4]
            value *= sum(int(left is not None and left[1] == a)
                         * int(right is not None and right[0] == a) for a in (0, 1))
        assert value == expected
    for mask in range(1, 15):
        side = [i for i in range(4) if mask >> i & 1]
        other = [i for i in range(4) if i not in side]
        columns = list(product(states, repeat=len(other)))
        rows = []
        for row in product(states, repeat=len(side)):
            bits = 0
            for j, col in enumerate(columns):
                assignment = dict(zip(side, row)) | dict(zip(other, col))
                if all(assignment[i][1] == assignment[(i + 1) % 4][0] for i in range(4)):
                    bits |= 1 << j
            rows.append(bits)
        crosses = sum((i in side) != ((i + 1) % 4 in side) for i in range(4))
        assert gf2_rank(rows) == 2**crosses


if __name__ == "__main__":
    check_collisions()
    check_grid()
    print("48 perturbed 3-cycle outputs, strict truncation witness")
    print("625 partial grid assignments, 14 exact binary cut ranks")
