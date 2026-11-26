"""Exhaustive four-bit rank-two covers and direct binary circuit comparisons."""
from itertools import combinations
from random import Random


def rank(columns):
    pivots = {}
    for value in columns:
        while value:
            row = value.bit_length()
            if row not in pivots:
                pivots[row] = value
                break
            value ^= pivots[row]
    return len(pivots)


def xor(columns):
    total = 0
    for x in columns:
        total ^= x
    return total


def finite_covers():
    planes = {tuple(sorted((a,b,a^b))) for a,b in combinations(range(1,16),2)}
    assert len(planes) == 35
    checked = failed = 0
    for n in range(8):
        for holes in combinations(range(1,16),n):
            block = all(any(v in holes for v in plane) for plane in planes)
            assert block == (n == 7 and rank(holes) == 3)
            checked += 1
            failed += block
    return checked,failed


def matrices():
    rng = Random(7901)
    checked = 0
    for _ in range(160):
        r = rng.randrange(1,5)
        q = rng.randrange(4)
        n = rng.randrange(1,9)
        base = [rng.randrange(2**r) for _ in range(n)]
        label = [rng.randrange(2**q) for _ in range(n)]
        demand = rng.randrange(1,2**r)
        target = rng.randrange(2**q)
        k = [1 << (r+i) for i in range(q)]
        terminals = k + [demand ^ (target << r) ^ xor(k)]
        for mask in range(1<<n):
            support = [j for j in range(n) if mask >> j & 1]
            columns = [base[j] for j in support]
            expected = (rank(columns) == len(columns)
                        and xor(columns) == demand and xor(label[j] for j in support) == target)
            full = terminals + [base[j] ^ (label[j] << r) for j in support]
            assert expected == (xor(full) == 0 and rank(full) == len(full)-1)
            checked += 1
    return checked


if __name__ == "__main__":
    print("tested sets, seven-hole obstructions:", finite_covers())
    print("tested supports:", matrices())
