"""Deterministic affine hitting-set search for mixed binary primal/dual tests."""
from functools import cache
from solver import basis, bits, parity, reduce_with_trace


def poly_mod(a, b):
    """Remainder for bit-packed binary polynomials; b must be nonzero."""
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def poly_gcd(a, b):
    while b:
        a, b = b, poly_mod(a, b)
    return a


def multiply(a, b, modulus):
    """Multiply residue classes modulo a monic binary polynomial."""
    result = 0
    top = 1 << (modulus.bit_length() - 1)
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & top:
            a ^= modulus
    return result


def irreducible(candidate):
    degree = candidate.bit_length() - 1
    if degree < 1:
        return False
    # Every reducible polynomial has an irreducible factor of degree ≤ degree/2.
    # A factor of degree i divides X^(2^i)-X.
    indeterminate = poly_mod(2, candidate)
    power = indeterminate
    for _ in range(1, degree//2 + 1):
        power = multiply(power, power, candidate)
        if poly_gcd(candidate, power ^ indeterminate) != 1:
            return False
    return True


@cache
def field_modulus(degree):
    if degree < 1:
        raise ValueError("field degree must be positive")
    for candidate in range((1 << degree) | 1, 1 << (degree+1), 2):
        if irreducible(candidate):
            return candidate
    raise AssertionError("no irreducible polynomial of specified degree")


def field_trace(a, modulus):
    result = 0
    for _ in range(modulus.bit_length()-1):
        result ^= a
        a = multiply(a, a, modulus)
    return result


def trace_points(dimension, codimension):
    """The explicit trace construction, including repeated points, streamed."""
    if dimension < 0 or codimension < 0:
        raise ValueError("negative hitting-set parameter")
    if not dimension:
        yield 0
        return
    degree = dimension.bit_length() + codimension
    q = 1 << degree
    modulus = field_modulus(degree)
    trace_mask = sum(field_trace(1 << j, modulus) << j for j in range(degree))
    yield 0
    for y in range(q):
        # Column j gives the point for x equal to the jth field basis vector.
        # Linearity in x lets Gray enumeration update one column at a time.
        columns = []
        for j in range(degree):
            value = 1 << j
            column = 0
            for i in range(dimension):
                column |= parity(value & trace_mask) << i
                value = multiply(value, y, modulus)
            columns.append(column)
        point = 0
        for index in range(1, q):
            changed = (index & -index).bit_length() - 1
            point ^= columns[changed]
            yield point


def hitting_points(dimension, codimension):
    if min(dimension, codimension) < 0:
        raise ValueError("negative hitting-set parameter")
    if not codimension:
        yield 0
    elif dimension <= 2*(dimension.bit_length()+codimension):
        yield from range(1 << dimension)
    else:
        yield from trace_points(dimension, codimension)


def affine_space(rank, equations):
    """Return (particular solution, free directions), or None if inconsistent."""
    rows = {}
    for mask, rhs in equations:
        while mask:
            j = mask.bit_length() - 1
            if j not in rows:
                rows[j] = mask, rhs
                break
            pivot, value = rows[j]
            mask ^= pivot
            rhs ^= value
        else:
            if rhs:
                return None
    ordered = sorted(rows.items())

    def complete(x, homogeneous):
        for j,(mask,rhs) in ordered:
            x |= (parity(mask & x) ^ (0 if homogeneous else rhs)) << j
        return x

    return complete(0, False), [complete(1 << i, True) for i in range(rank) if i not in rows]


def solve(rank, labels, ordinary, flat_codim, t, target=0, root_label=0,
          moments=(), dual_tests=(), s=None):
    """Return (d, ordinary occurrence mask) or None under the flat promise.

    flat_codim is an upper bound on the RELATIVE codimension of an affine flat
    of feasible duals inside the base-test solution space, whenever feasible.
    For a lifted strong blocking space of codimension h use h+min(h,labels).
    """
    if min(rank, labels, flat_codim) < 0:
        raise ValueError("negative dimension or codimension")
    ordinary = list(ordinary)
    moments = list(moments) or [0]*labels
    tests = list(dual_tests) + [(t,0)]
    if s is not None:
        tests.append((s,1))
    if (len(moments) != labels or any(not 0 <= m < 1 << rank for m in moments)
        or any(not 0 <= m < 1 << rank or b not in (0,1) for m,b in tests)
        or any(not 0 <= v < 1 << rank or not 0 <= w < 1 << labels for v,w in ordinary)
        or any(not 0 <= w < 1 << labels for w in (target,root_label))):
        raise ValueError("invalid mask, equation, or dimension")
    space = affine_space(rank, tests)
    if space is None:
        return None
    origin, directions = space
    for point in hitting_points(len(directions), flat_codim):
        d = origin
        for j in bits(point):
            d ^= directions[j]
        requested = target ^ root_label
        for j, mask in enumerate(moments):
            requested ^= parity(mask & d) << j
        eligible = [i for i,(v,_) in enumerate(ordinary) if not parity(v & d)]
        lifted = (ordinary[i][0] | (ordinary[i][1] << rank) for i in eligible)
        residual, trace = reduce_with_trace(t | (requested << rank), basis(lifted))
        if not residual:
            return d, sum(1 << eligible[j] for j in bits(trace))
    return None
