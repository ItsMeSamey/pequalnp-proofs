"""Scalar contraction on the shared Fourier subspaces of an affine CSP."""
from itertools import product
from fractions import Fraction
from random import Random


def span(rows):
    values = {0}
    for row in rows:
        values |= {row ^ s for s in values}
    return values


def parity(v):
    return v.bit_count() % 2


def value(factor, x):
    rows, table = factor
    index = sum(parity(row & x) << i for i, row in enumerate(rows))
    return table[index]


def count(d, factors):
    # Small reference implementation materializes spans to check the recurrence.
    # A scalable implementation uses binary bases to construct intersections.
    def visit(indices):
        inside = set(indices)
        rows = [r for i in indices for r in factors[i][0]]
        external = [r for i in range(len(factors)) if i not in inside for r in factors[i][0]]
        boundary = span(rows) & span(external)
        if len(indices) == 1:
            f = factors[indices[0]]
            return {s: Fraction(sum((-1)**parity(s & x) * value(f, x) for x in range(1 << d)), 1 << d) for s in boundary}
        m = len(indices)//2
        left = visit(indices[:m])
        right = visit(indices[m:])
        return {s: sum(v * right.get(s ^ a, 0) for a,v in left.items()) for s in boundary}
    return (1 << d) * visit(list(range(len(factors))))[0]


rng = Random(793)
for _ in range(150):
    d = rng.randrange(1, 8)
    fs = []
    for _ in range(rng.randrange(1, 9)):
        rows = [rng.randrange(1 << d) for _ in range(rng.randrange(1, 4))]
        fs.append((rows, [rng.randrange(2) for _ in range(1 << len(rows))]))
    brute = sum(all(value(f,x) for f in fs) for x in range(1 << d))
    assert count(d, fs) == brute
print('150 scalar contractions matched exhaustive counts')
