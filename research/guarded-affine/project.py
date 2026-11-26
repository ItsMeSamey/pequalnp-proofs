"""Project to a disjunction of multilinear polynomials over GF(2).
A polynomial is the set of masks of its monomials. Mask 0 is constant one.
"""
from itertools import product


def affine(mask, bias):
    terms = {0} if bias else set()
    while mask:
        bit = mask & -mask
        terms.add(bit)
        mask ^= bit
    return frozenset(terms)


def multiply(a, b):
    terms = set()
    for s, t in product(a, b):
        m = s | t
        if m in terms:
            terms.remove(m)
        else:
            terms.add(m)
    return frozenset(terms)


def basis(polynomials):
    rows = {}
    for p in polynomials:
        while p:
            pivot = max(p)
            if pivot not in rows:
                rows[pivot] = p
                break
            p = p ^ rows[pivot]
    return list(rows.values())


def step(polynomials, bit, guards):
    for p in polynomials:
        yield frozenset(t for t in p if not t & bit)
        derivative = frozenset(t ^ bit for t in p if t & bit)
        for g in guards:
            yield multiply(derivative, g)


def compile_projection(observed, guards, terminal):
    """Observed bits precede hidden bits in guard order."""
    if observed < 0:
        raise ValueError("negative observed bit count")
    for j, clause in enumerate(guards):
        if any(m < 0 or m >= 1 << (observed + j + 1) or b not in (0, 1)
               for m, b in clause):
            raise ValueError("malformed guard or dependency on a later bit")
    tests = [frozenset({0})]
    for clause in terminal:
        if any(m < 0 or m >= 1 << (observed + len(guards)) or b not in (0, 1)
               for m, b in clause):
            raise ValueError("invalid terminal literal")
        forms = [affine(mask, bias) for mask, bias in clause]
        tests = basis(multiply(p, g) for p in tests for g in forms)
    for j in reversed(range(len(guards))):
        bit = 1 << (observed + j)
        forms = [affine(m & ~bit, b ^ int(bool(m & bit))) for m, b in guards[j]]
        tests = basis(step(tests, bit, forms))
    return tests


def evaluate(tests, x):
    return any(sum((x & mask) == mask for mask in p) % 2 for p in tests)
