"""Exact signed counts for quadratic leaves sharing binary variables.

Polynomials are frozensets of squarefree monomial masks (0 is the constant).
Each leaf numbers its shared bits first, then its own private bits. Equations
have target zero. The exponent of each optional character is added to the phase.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from random import Random


ZERO = frozenset()
ONE = frozenset({0})


def multiply(left, right):
    result = set()
    for a in left:
        for b in right:
            mask = a | b
            result.symmetric_difference_update([mask])
    return frozenset(result)


def check_poly(poly, nbits):
    if any(mask < 0 or mask.bit_length() > nbits or mask.bit_count() > 2
           for mask in poly):
        raise ValueError("expected a squarefree quadratic in the declared bits")


def affine_domain(equations):
    """Canonical RREF of (bitmask, rhs) equations, or None if inconsistent."""
    basis = {}
    for row, rhs in equations:
        for pivot in sorted(basis):
            if row & pivot:
                old, value = basis[pivot]
                row ^= old
                rhs ^= value
        if not row:
            if rhs:
                return None
            continue
        pivot = row & -row
        for other, (old, value) in list(basis.items()):
            if old & pivot:
                basis[other] = (old ^ row, value ^ rhs)
        basis[pivot] = row, rhs
    return tuple(basis[k] for k in sorted(basis))


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def restrict(phase, domain):
    """Substitute pivot coordinates by affine functions of the free bits."""
    substitution = {}
    for row, rhs in domain:
        pivot = row & -row
        substitution[pivot] = frozenset(bits(row ^ pivot)) ^ (ONE if rhs else ZERO)
    result = ZERO
    for monomial in phase:
        term = ONE
        for variable in bits(monomial):
            term = multiply(term, substitution.get(variable, frozenset({variable})))
        result ^= term
    return result


def private_sum(phase, private):
    """Return (weight, domain, phase) for the unnormalized private Walsh sum."""
    original_count = private.bit_count()
    pivots = 0
    while True:
        pair = next((m for m in sorted(phase)
                     if (m & private).bit_count() == 2), None)
        if pair is None:
            break
        u, v = bits(pair)
        left = frozenset(m ^ u for m in phase if m != pair and m & u)
        right = frozenset(m ^ v for m in phase if m != pair and m & v)
        phase = frozenset(m for m in phase if not m & pair) ^ multiply(left, right)
        private ^= pair
        pivots += 1

    equations = []
    for variable in bits(private):
        coeff = frozenset(m ^ variable for m in phase if m & variable)
        equations.append((sum(coeff - {0}), int(0 in coeff)))
    domain = affine_domain(equations)
    if domain is None:
        return 0, (), ZERO
    residual = frozenset(m for m in phase if not m & private)
    return 1 << (original_count - pivots), domain, restrict(residual, domain)


def insert(table, domain, phase, weight):
    """Group equal restricted phases and absorb a constant sign in the weight."""
    if 0 in phase:
        weight = -weight
        phase ^= ONE
    if weight:
        key = domain, phase
        table[key] += weight
        if not table[key]:
            del table[key]


def leaf_expansion(shared, leaf):
    private_count, guards, character = leaf
    for poly in (*guards, character):
        check_poly(poly, shared + private_count)
    private = ((1 << private_count) - 1) << shared
    table = defaultdict(Fraction)
    for subset in range(1 << len(guards)):
        phase = character
        for bit in bits(subset):
            phase ^= guards[bit.bit_length() - 1]
        weight, domain, residual = private_sum(phase, private)
        insert(table, domain, residual, Fraction(weight, 1 << len(guards)))
    return table


def signed_count(shared, leaves, character=ZERO):
    check_poly(character, shared)
    table = {((), character): Fraction(1)}
    for leaf in leaves:
        expansion = leaf_expansion(shared, leaf)
        joined = defaultdict(Fraction)
        for (left, p), a in table.items():
            for (right, q), b in expansion.items():
                domain = affine_domain((*left, *right))
                if domain is not None:
                    insert(joined, domain, restrict(p ^ q, domain), a * b)
        table = joined
    total = Fraction()
    for (domain, phase), coeff in table.items():
        free = (1 << shared) - 1
        for row, _ in domain:
            free ^= row & -row
        weight, leftover, scalar = private_sum(phase, free)
        assert not leftover and scalar in (ZERO, ONE)
        total += coeff * weight * (-1 if scalar else 1)
    assert total.denominator == 1
    return int(total)


def evaluate(poly, assignment):
    return sum(assignment & m == m for m in poly) % 2


def brute(shared, leaves, character):
    total = 0
    for x in range(1 << shared):
        value = (-1) ** evaluate(character, x)
        for n, guards, local_character in leaves:
            count = 0
            for z in range(1 << n):
                assignment = x | (z << shared)
                if not any(evaluate(g, assignment) for g in guards):
                    count += (-1) ** evaluate(local_character, assignment)
            value *= count
        total += value
    return total


def run_tests():
    rng = Random(230179)

    def polynomial(n):
        terms = [0, *(1 << j for j in range(n))]
        terms.extend((1 << j) | (1 << k) for j, k in combinations(range(n), 2))
        return frozenset(m for m in terms if rng.randrange(3) == 0)

    # Exhaust all phases on two private bits and one shared bit.
    monomials = (0, 1, 2, 4, 3, 5, 6)
    for vector in product(range(2), repeat=len(monomials)):
        phase = frozenset(m for m, use in zip(monomials, vector) if use)
        weight, domain, residual = private_sum(phase, 6)
        for x in range(2):
            allowed = all((x & row).bit_count() % 2 == rhs for row, rhs in domain)
            got = weight * allowed * (-1) ** evaluate(residual, x)
            expected = sum((-1) ** evaluate(phase, x | (z << 1)) for z in range(4))
            assert got == expected

    for _ in range(450):
        shared = rng.randrange(6)
        character = polynomial(shared)
        leaves = []
        for _ in range(rng.randrange(5)):
            n = rng.randrange(5)
            guards = [polynomial(shared + n) for _ in range(rng.randrange(4))]
            leaves.append((n, guards, polynomial(shared + n)))
        assert signed_count(shared, leaves, character) == brute(shared, leaves, character)
    print("128 exhaustive private phases and 450 seeded joint counts passed")


if __name__ == "__main__":
    run_tests()
