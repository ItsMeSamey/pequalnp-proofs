"""Check bucket-wise diagonal evaluation after formal residual truncation."""
from itertools import combinations
from random import Random


def check_trial(case, rng):
    prime = (3, 5, 7)[case % 3]
    precision = 2 + case % 2
    modulus = prime ** precision
    n = 5
    point = [rng.randrange(2) for _ in range(n)]
    off_group = [rng.randrange(modulus) for _ in range(n)]
    variation = [rng.randrange(modulus) for _ in range(n)]
    base = sum(x * y for x, y in zip(point, off_group)) % prime
    constants = [rng.randrange(modulus) for _ in range(5)]

    def coefficient(probe, jet_order, residual_order):
        delta = sum(x * y for x, y in zip(probe, off_group)) - base
        jet = sum(x * y for x, y in zip(probe, variation))
        table = {(0, 0): 1}
        for constant in constants:
            table = {
                (j, s): (
                    (constant + base) * table.get((j, s), 0)
                    + delta * table.get((j, s - 1), 0)
                    + jet * table.get((j - 1, s), 0)
                ) % modulus
                for j in range(jet_order + 1) for s in range(residual_order + 1)
            }
        return table[jet_order, residual_order]

    ones = [i for i, value in enumerate(point) if value]
    for j in range(3):
        expected = sum(coefficient(point, j, s) for s in range(6))
        recovered = 0
        for s in range(precision):
            for d in range(min(j + s, len(ones)) + 1):
                for support in combinations(ones, d):
                    for u in range(d + 1):
                        for subset in combinations(support, u):
                            probe = [int(i in subset) for i in range(n)]
                            recovered += (-1) ** (d - u) * coefficient(probe, j, s)
        assert (expected - recovered) % modulus == 0


if __name__ == "__main__":
    rng = Random(47)
    for case in range(180):
        check_trial(case, rng)
    print("540 bucketwise p-adic finite-difference jet comparisons passed")
