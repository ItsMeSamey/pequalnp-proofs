"""Exact finite checks for witness records and random greedy-basis changes."""
from fractions import Fraction
from itertools import permutations
from math import comb, factorial

def harmonic(t):
    return sum((Fraction(1, i) for i in range(1, t+1)), Fraction())

def records(order, priority):
    best = len(order)
    total = 0
    for elem in order:
        if priority[elem] < best:
            total += 1
            best = priority[elem]
    return total

def basis(rows, keys, t):
    span = {0}
    accepted = set()
    for i in sorted(range(t), key=keys.__getitem__):
        if rows[i] not in span:
            accepted.add(i)
            span |= {x ^ rows[i] for x in span}
    return accepted

def exact_matroid(rows, order):
    rows = [rows[i] for i in order]
    m = len(rows)
    expected = 0
    for keys in permutations(range(m)):
        expected += sum(t-1 in basis(rows, keys, t) for t in range(1, m+1))
    expected = Fraction(expected, factorial(m))
    integral = Fraction()
    for bits in range(1, 1 << m):
        subset = [a for i, a in enumerate(rows) if bits & (1 << i)]
        s = len(subset)
        rank = len(basis(subset, list(range(s)), s))
        # Integral u^(s-1) (1-u)^(m-s) du = 1/(s binom(m,s)).
        integral += Fraction(rank, s * comb(m, s))
    assert expected == integral
    r = len(basis(rows, list(range(m)), m))
    assert expected <= r * (1 + harmonic(m) - harmonic(r))
    return expected

if __name__ == "__main__":
    for q in range(1, 7):
        assert Fraction(sum(records(range(q), p) for p in permutations(range(q))), factorial(q)) == harmonic(q)
    for rows in ([1, 1, 1, 1], [1, 2, 3, 4, 5], [0, 1, 1, 2, 2, 3], [1, 2, 4, 8]):
        m = len(rows)
        f = exact_matroid(rows, range(m))
        assert exact_matroid(rows, reversed(range(m))) == f
        print("row family", rows, "expected basis insertions", f)
    print("harmonic records checked exactly through 6 feasible choices")
