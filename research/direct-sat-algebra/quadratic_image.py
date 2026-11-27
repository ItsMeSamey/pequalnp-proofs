"""Deterministic, output-polynomial discovery of a binary quadratic map's image.

discover(n, forms) returns {packed_output: (exact_fiber_count, packed_witness)}.
Bit j denotes coordinate j, starting at zero. Running this file executes controls.

For m coordinates and K distinct outputs, the largest field cardinality Q is
O(1+m*K*K): a guess in [K,2K) suffices by the polynomial root bound for
pairwise differences. For smaller guesses a hash is accepted only if every
output bit is constant in every nonempty bucket. Walsh inversion over the
additive binary group computes each bucket mass and each signed bit sum;
equality in absolute value detects constancy since masses are integer counts.
Fixing variables one at a time in the successful bucket gives a witness.

Across a round using field size Q there are at most (m+1)*Q*Q Gauss sums
to check all hashes, then at most n*K*Q more to recover witnesses on success.
There are O(1+log K) rounds. Each Gauss sum has magnitude <= 2^n; Walsh
intermediates and witness sums have O(1+n+log Q) bits. At most n/2 pair
eliminations per Gauss sum each perform O(n^2) pair updates. Indices, masks,
field arithmetic, finite-set operations and trial-divisor field construction
all have polynomial bit cost in n,m,Q and input length (including input
normalization). These operation counts do not assume unit-cost arithmetic
on unbounded integers or a precomputed finite-field oracle. The representation
stores O(Q) quadratic forms of O(n^2) pairs each plus spectra and output.
"""

from dataclasses import dataclass
from itertools import combinations
from random import Random


@dataclass(frozen=True)
class Quadratic:
    constant: int = 0
    linear: int = 0
    pairs: tuple = ()


def add(f, g):
    return f[0] ^ g[0], f[1] ^ g[1], f[2] ^ g[2]


ZERO = (0, 0, frozenset())


def normalize(n, form):
    c, linear = form.constant, form.linear
    if c not in (0, 1) or not 0 <= linear < 1 << n:
        raise ValueError("invalid constant or linear mask")
    pairs = set()
    for i, j in form.pairs:
        if not (0 <= i < n and 0 <= j < n):
            raise ValueError("quadratic index out of range")
        if i == j:
            linear ^= 1 << i
        else:
            pairs.symmetric_difference_update([(min(i, j), max(i, j))])
    return c, linear, frozenset(pairs)


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def parity(mask):
    return mask.bit_count() & 1


def gauss(n, f, fixed=0, values=0):
    """Sum (-1)^f on the indicated coordinate slice, by hyperbolic pair removal."""
    c, linear, original = f
    c ^= parity(linear & fixed & values)
    linear &= ~fixed
    pairs = set()
    for i, j in original:
        bi, bj = 1 << i, 1 << j
        if fixed & bi and fixed & bj:
            c ^= int(bool(values & bi and values & bj))
        elif fixed & bi:
            if values & bi:
                linear ^= bj
        elif fixed & bj:
            if values & bj:
                linear ^= bi
        else:
            pairs.add((i, j))
    free = n - fixed.bit_count()
    removed_pairs = 0
    while pairs:
        i, j = next(iter(pairs))
        pairs.remove((i, j))
        ci, cj = (linear >> i) & 1, (linear >> j) & 1
        linear &= ~((1 << i) | (1 << j))
        adjacent_i = adjacent_j = 0
        rest = set()
        for u, v in pairs:
            if i in (u, v):
                adjacent_i |= 1 << (u ^ v ^ i)
            elif j in (u, v):
                adjacent_j |= 1 << (u ^ v ^ j)
            else:
                rest.add((u, v))
        # Sum over i,j equals 2 times the sign of the product of affine neighbors.
        c ^= ci & cj
        if ci:
            linear ^= adjacent_j
        if cj:
            linear ^= adjacent_i
        linear ^= adjacent_i & adjacent_j
        for u in bits(adjacent_i):
            for v in bits(adjacent_j & ~(1 << u)):
                rest.symmetric_difference_update([(min(u, v), max(u, v))])
        pairs = rest
        removed_pairs += 1
    return 0 if linear else (-1 if c else 1) << (free - removed_pairs)


def remainder(p, d):
    while p.bit_length() >= d.bit_length():
        p ^= d << (p.bit_length() - d.bit_length())
    return p


def field_modulus(k):
    # Trial divisors suffice in time polynomial in the field cardinality.
    for p in range(1 << k, 2 << k):
        if all(remainder(p, d) for d in range(2, 1 << (k // 2 + 1))):
            return p
    raise ArithmeticError("no irreducible polynomial")


def multiply(a, b, p):
    acc = 0
    for i in bits(b):
        acc ^= a << i
    return remainder(acc, p)


def hash_forms(forms, a, k, p):
    masks = [ZERO for _ in range(k)]
    power = 1
    for f in forms:
        for j in bits(power):
            masks[j] = add(masks[j], f)
        power = multiply(power, a, p)
    chars = [ZERO]
    for f in masks:
        chars.extend([add(t, f) for t in chars])
    return chars


def spectrum(n, chars, extra=ZERO):
    """Unnormalized Walsh transform, divided exactly by its length."""
    weights = [gauss(n, add(q, extra)) for q in chars]
    step = 1
    while step < len(weights):
        for start in range(0, len(weights), 2 * step):
            for j in range(start, start + step):
                x, y = weights[j], weights[j + step]
                weights[j], weights[j + step] = x + y, x - y
        step *= 2
    assert all(w % len(chars) == 0 for w in weights)
    return [w // len(chars) for w in weights]


def fiber_witness(n, chars, bucket):
    fixed = values = 0
    for j in range(n):
        fixed |= 1 << j
        zero_mass = sum((-1 if parity(u & bucket) else 1) *
                        gauss(n, q, fixed, values) for u, q in enumerate(chars))
        if zero_mass == 0:
            values |= 1 << j
    return values


class FieldBudgetExceeded(RuntimeError):
    """The next deterministic hash family exceeds the specified field cap."""


def discover(n, forms, *, max_field_size=None):
    if n < 0:
        raise ValueError("negative dimension")
    forms = [normalize(n, f) for f in forms]
    guess = 1
    while True:
        # Any distinct output pair excludes at most m-1 choices of a.
        degree = max(0, len(forms) - 1)
        k = max(1, (degree * guess * (guess - 1) // 2).bit_length())
        if max_field_size is not None and 1 << k > max_field_size:
            raise FieldBudgetExceeded(f"next field has {1 << k} elements")
        p = field_modulus(k)
        for a in range(1 << k):
            chars = hash_forms(forms, a, k, p)
            masses = spectrum(n, chars)
            buckets = [b for b, count in enumerate(masses) if count]
            outputs = {b: 0 for b in buckets}
            for j, f in enumerate(forms):
                signed = spectrum(n, chars, f)
                if any(abs(signed[b]) != masses[b] for b in buckets):
                    break
                for b in buckets:
                    if signed[b] < 0:
                        outputs[b] |= 1 << j
            else:
                return {outputs[b]: (masses[b], fiber_witness(n, chars, b))
                        for b in buckets}
        guess *= 2


def evaluate(forms, x):
    def value(f):
        return (f.constant ^ parity(f.linear & x) ^
                (sum(((x >> i) & (x >> j) & 1) for i, j in f.pairs) & 1))
    return sum(value(f) << j for j, f in enumerate(forms))


def check():
    rng = Random(34870)
    cases = [(0, []), (5, []), (0, [Quadratic(1)] * 15),
             (4, [Quadratic(0, 1 << j) for j in range(4)]),
             (18, [Quadratic(0, 0, ((0, 1),))] * 23)]
    for _ in range(50):
        n, m = rng.randrange(6), rng.randrange(5)
        forms = [Quadratic(rng.randrange(2), rng.randrange(1 << n),
                           tuple(pair for pair in combinations(range(n), 2)
                                 if rng.randrange(2))) for _ in range(m)]
        cases.append((n, forms))
    cases.append((2, [Quadratic(0, 0, ((1, 0), (0, 1), (1, 1)))]))
    for n, forms in cases:
        got = discover(n, forms)
        if n == 18:
            expected = {0: 3 << 16, (1 << 23) - 1: 1 << 16}
        else:
            expected = {}
            for x in range(1 << n):
                y = evaluate(forms, x)
                expected[y] = expected.get(y, 0) + 1
        assert expected == {y: count for y, (count, _) in got.items()}
        assert all(evaluate(forms, x) == y for y, (_, x) in got.items())
    print(f"{len(cases)} exact image/count/witness controls passed")


if __name__ == "__main__":
    check()
