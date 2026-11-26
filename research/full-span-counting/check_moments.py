#!/usr/bin/env python3
"""Exact tests for a zero-mass estimator using only a sequential moment oracle."""
from fractions import Fraction
from itertools import product
from math import comb


def solve(matrix, target):
    rows = [list(map(Fraction, row + [b])) for row, b in zip(matrix, target)]
    for i in range(len(rows)):
        pivot = next((j for j in range(i, len(rows)) if rows[j][i]), None)
        assert pivot is not None
        rows[i], rows[pivot] = rows[pivot], rows[i]
        scale = rows[i][i]
        rows[i] = [v / scale for v in rows[i]]
        for j in range(len(rows)):
            if j != i:
                scale = rows[j][i]
                rows[j] = [v - scale * w for v, w in zip(rows[j], rows[i])]
    return [row[-1] for row in rows]


def recover(oracle):
    # At first zero Schur complement, the monic residual polynomial vanishes
    # on every support point, by positivity of the empirical measure.
    moments = [oracle(0)]
    if not moments[0]:
        return Fraction(0), 0
    d = 1
    while True:
        moments.extend([oracle(2*d-1), oracle(2*d)])
        gram = [[moments[i+j] for j in range(d)] for i in range(d)]
        target = moments[d:2*d]
        coeff = solve(gram, target)
        if moments[2*d] == sum(a*b for a, b in zip(coeff, target)):
            polynomial = [-a for a in coeff] + [Fraction(1)]
            if polynomial[0]:
                return Fraction(0), d
            # P(X)/X divided by P'(0) is the indicator of zero on the support.
            assert polynomial[1]
            return sum(a*b for a, b in zip(polynomial[1:], moments)) / polynomial[1], d
        d += 1


def moment(hist, k):
    return sum(count * x**k for x, count in enumerate(hist))


def main():
    checked = 0
    for hist in product(range(3), repeat=5):
        mass, rank = recover(lambda k: moment(hist, k))
        assert mass == hist[0]
        assert rank == sum(count > 0 for count in hist)
        checked += 1
    for n in range(1, 17):
        even = [comb(n,i) if i % 2 == 0 else 0 for i in range(n+1)]
        odd = [comb(n,i) if i % 2 else 0 for i in range(n+1)]
        assert even[0] == 1 and odd[0] == 0
        assert all(moment(even,k) == moment(odd,k) for k in range(n))
        assert moment(even,n) != moment(odd,n)
    print(f"{checked} histograms recovered exactly; 16 even/odd moment collisions verified.")


if __name__ == "__main__":
    main()
