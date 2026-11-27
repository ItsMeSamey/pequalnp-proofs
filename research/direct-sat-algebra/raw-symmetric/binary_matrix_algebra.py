"""Radical and orthogonal lifts of primitive central atoms of A/J over GF(2).
Matrices are packed column-first, n bits per column. analyze(n,basis) checks
that the independent input basis spans a matrix algebra containing I.
The lifted idempotents need not be central in A.
"""
from dataclasses import dataclass
from quadratic_centroid import independent, zero_combinations
from quadratic_target import apply_basis, reduce_vector


def cols(n, a):
    return tuple((a >> (i*n)) & ((1 << n)-1) for i in range(n))


def product(n, a, b):
    u = cols(n, a)
    return sum(apply_basis(u, v) << (j*n) for j, v in enumerate(cols(n, b)))


def echelon(vectors):
    rows = {}
    for v in vectors:
        reduced, _ = reduce_vector(v, rows)
        if reduced:
            rows[reduced.bit_length()-1] = reduced, 0
    return rows


def polymul(a, b):
    v = 0
    while b:
        bit = b & -b
        v ^= a << (bit.bit_length()-1)
        b ^= bit
    return v


def exact_div(a, b):
    if not b:
        raise ZeroDivisionError
    q = 0
    while a.bit_length() >= b.bit_length():
        shift = a.bit_length() - b.bit_length()
        q ^= 1 << shift
        a ^= b << shift
    if a:
        raise ArithmeticError("inexact Bareiss division")
    return q


def characteristic(n, a):
    """det(XI+A), bit i denotes the coefficient of X^i."""
    rows = [[((a >> (j*n+i)) & 1) ^ (2 if i == j else 0)
             for j in range(n)] for i in range(n)]
    previous = 1
    for i in range(n-1):
        r = next((j for j in range(i, n) if rows[j][i]), None)
        if r is None:
            return 0
        rows[i], rows[r] = rows[r], rows[i]
        pivot = rows[i][i]
        for j in range(i+1, n):
            for k in range(i+1, n):
                numerator = polymul(pivot, rows[j][k]) ^ polymul(rows[j][i], rows[i][k])
                rows[j][k] = exact_div(numerator, previous)
            rows[j][i] = 0
        previous = pivot
    return rows[-1][-1] if n else 1


@dataclass(frozen=True)
class Structure:
    radical: tuple
    filtration_dimensions: tuple
    quotient_central_atoms: tuple
    lifts: tuple


def analyze(n, basis):
    basis = tuple(basis)
    if n < 1 or any(not isinstance(a, int) or not 0 <= a < 1 << (n*n) for a in basis):
        raise ValueError("invalid binary matrix size or encoding")
    space = echelon(basis)
    one = sum(1 << (j*n+j) for j in range(n))
    def mul(a, b):
        return product(n, a, b)
    if (len(space) != len(basis) or reduce_vector(one, space)[0] or
            any(reduce_vector(mul(a, b), space)[0] for a in basis for b in basis)):
        raise ValueError("basis does not define a unital matrix algebra")
    layer = basis
    dimensions = [len(layer)]
    for k in range(n.bit_length()):
        order = 1 << k
        def pairing_row(x):
            return sum(((characteristic(n, mul(x, y)) >> (n-order)) & 1) << j
                       for j, y in enumerate(basis))
        layer = tuple(zero_combinations(layer, pairing_row))
        dimensions.append(len(layer))
    radical = echelon(layer)
    def quotient(a):
        return reduce_vector(a, radical)[0]
    qbasis = independent(quotient(a) for a in basis)
    def commutators(x):
        return sum(quotient(mul(x, y) ^ mul(y, x)) << (j*n*n) for j, y in enumerate(qbasis))
    center = zero_combinations(qbasis, commutators)
    fixed = zero_combinations(center, lambda x: quotient(mul(x, x) ^ x))
    atoms = [quotient(one)]
    for e in fixed:
        refined = []
        for a in atoms:
            part = quotient(mul(a, e))
            if part:
                refined.append(part)
            if a ^ part:
                refined.append(a ^ part)
        atoms = refined
    # Work in successive complementary corners so the lifts stay orthogonal.
    lifts = []
    remaining = one
    for a in atoms:
        v = mul(mul(remaining, a), remaining)
        for _ in range((n-1).bit_length()):
            v = mul(v, v)
        if (mul(v, v) != v or quotient(v) != a or
                mul(remaining, v) != v or mul(v, remaining) != v):
            raise ArithmeticError("invalid atom lift")
        lifts.append(v)
        remaining ^= v
    if remaining:
        raise ArithmeticError("atom lifts did not exhaust identity")
    return Structure(tuple(layer), tuple(dimensions), tuple(atoms), tuple(lifts))


def check():
    def unit(n, i, j):
        return 1 << (j*n+i)
    def diag(n, indices):
        return sum(unit(n,j,j) for j in indices)
    def verify(n, basis, rad, atom_count):
        s = analyze(n, basis)
        assert len(s.radical) == len(rad) and len(independent([*rad,*s.radical])) == len(rad)
        assert len(s.lifts) == atom_count
        for i, a in enumerate(s.lifts):
            for j, b in enumerate(s.lifts):
                assert product(n,a,b) == (a if i == j else 0)
        return s
    n = 2
    all_units = [unit(n,i,j) for i in range(n) for j in range(n)]
    verify(n, all_units, [], 1)
    eps = unit(n,0,1)
    verify(n, [diag(n,range(n)),eps], [eps], 1)
    verify(n, [diag(n,[0]),diag(n,[1]),eps], [eps], 2)
    n = 4
    e = diag(n,[0,1])
    alpha = unit(n,1,0) ^ unit(n,0,1) ^ unit(n,1,1)
    f = diag(n,[2,3])
    eps = unit(n,2,3)
    verify(n,[e^eps,alpha^f,f^eps,eps],[eps],2)
    # Scalar factors have composition multiplicities 4 and 2.
    s = verify(6,[diag(6,range(4)),diag(6,[4,5])],[],2)
    assert s.filtration_dimensions == (2,2,1,0)
    n = 2
    tri = [diag(n,[0])^unit(n,0,1),diag(n,[1]),unit(n,0,1)]
    s = verify(n,tri,[unit(n,0,1)],2)
    assert all(any(product(n,a,b)!=product(n,b,a) for b in tri) for a in s.lifts)
    print("six matrix-algebra radical, multiplicity and central-atom controls passed")


if __name__ == "__main__":
    check()
