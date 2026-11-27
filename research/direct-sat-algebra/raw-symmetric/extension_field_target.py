"""Recognize a translated homogeneous field-quadratic map and count its targets.

prepare(n,m,c,linear,pairs) accepts packed squarefree vector ANF, returning
a FieldChart or None (inconclusive). chart.solve(target) returns an exact
fiber size and a checked ambient witness. No field elements are enumerated.
"""
from dataclasses import dataclass
from itertools import combinations
from quadratic_centroid import independent, zero_combinations
from quadratic_image import bits, gauss
from quadratic_target import apply_basis, evaluate_anf, insert, reduce_vector


def pack(columns, width):
    return sum(v << (j * width) for j, v in enumerate(columns))


def unpack(packed, size):
    mask = (1 << size) - 1
    return tuple((packed >> (j * size)) & mask for j in range(size))


def centroid(n, m, pairs):
    """Return a basis of paired input/output centroid actions, or None."""
    if len(independent(pairs.values())) != m:
        return None
    polar = [tuple(pairs.get(tuple(sorted((i, j))), 0) for i in range(n))
             for j in range(n)]
    unit = tuple(1 << i for i in range(n))
    if zero_combinations(unit, lambda x: pack((apply_basis(row, x) for row in polar), m)):
        return None

    def decode(v):
        return unpack(v, n), unpack(v >> (n*n), m)

    def defect(v):
        s, t = decode(v)
        return pack((apply_basis(row, sx) ^ apply_basis(t, cell)
                     for row in polar for sx, cell in zip(s, row)), m)

    kernel = zero_combinations((1 << j for j in range(n*n + m*m)), defect)
    return tuple(map(decode, kernel))


@dataclass
class FieldChart:
    n: int
    m: int
    offset: int
    shift: int
    count_zero: int
    count_nonzero: int
    seed: int
    scaling: dict
    actions: tuple
    anf: tuple

    def solve(self, target):
        if not 0 <= target < 1 << self.m:
            raise ValueError("target out of range")
        goal = target ^ self.offset
        count = self.count_nonzero if goal else self.count_zero
        if not count:
            return 0, None
        witness = self.shift
        if goal:
            remainder, scalars = reduce_vector(goal, self.scaling)
            if remainder:
                raise ArithmeticError("field action misses nonzero output")
            for j in bits(scalars):
                witness ^= apply_basis(self.actions[j], self.seed)
        if evaluate_anf(*self.anf, witness) != target:
            raise ArithmeticError("invalid scaled field witness")
        return count, witness


def prepare(n, m, constant, linear, pairs):
    if (min(n, m, constant) < 0 or len(linear) != n or
            any(not 0 <= v < 1 << m for v in (constant, *linear, *pairs.values())) or
            any(not 0 <= i < j < n for i, j in pairs)):
        raise ValueError("invalid packed quadratic")
    if not n or not m:
        return None
    actions = centroid(n, m, pairs)
    if actions is None or len(actions) != m:
        return None
    # Full output span and zero radical make the output action faithful.
    # Commutativity makes Frobenius linear. An injective Frobenius excludes
    # nilpotents, and the dimension of Fix(Frob) counts the field factors.
    squared = [tuple(apply_basis(t, col) for col in t) for _, t in actions]
    if (len(independent(pack(tt, m) for tt in squared)) != m or
            len(independent(pack(tt, m) ^ pack(t, m) for (_, t), tt in zip(actions, squared))) != m-1):
        return None

    linear, pairs = tuple(linear), dict(pairs)
    def q(x):
        return evaluate_anf(0, linear, pairs, x)

    def translated_linear(z):
        cols = list(linear)
        for (i, j), v in pairs.items():
            if (z >> i) & 1:
                cols[j] ^= v
            if (z >> j) & 1:
                cols[i] ^= v
        return cols

    def compatibility(z):
        l = translated_linear(z)
        return pack((evaluate_anf(0, l, pairs, sx) ^ apply_basis(tt, l[i])
                     for (s, _), tt in zip(actions, squared) for i, sx in enumerate(s)), m)

    delta = compatibility(0)
    rows = {}
    for j in range(n):
        insert(compatibility(1 << j) ^ delta, 1 << j, rows)
    rem, z = reduce_vector(delta, rows)
    if rem:
        return None
    if compatibility(z):
        raise ArithmeticError("translation fails field compatibility")
    l = translated_linear(z)
    seed = next((1 << i for i, y in enumerate(l) if y), 0)
    if not seed:
        seed = next(((1 << i) | (1 << j) for (i, j), y in pairs.items() if y), 0)
    y = evaluate_anf(0, l, pairs, seed)
    if not y:
        raise ArithmeticError("full span map has no nonzero quadratic seed")
    scaling = {}
    for j, tt in enumerate(squared):
        insert(apply_basis(tt, y), 1 << j, scaling)
    if len(scaling) != m:
        raise ArithmeticError("field square-scaling is not transitive")
    phase = (0, sum((v & 1) << i for i, v in enumerate(l)),
             frozenset(e for e, v in pairs.items() if v & 1))
    bias = gauss(n, phase)
    nonzero, rem = divmod((1 << n) - bias, 1 << m)
    zero = nonzero + bias
    if rem or min(zero, nonzero) < 1:
        raise ArithmeticError("inconsistent field fiber counts")
    return FieldChart(n, m, constant ^ q(z), z, zero, nonzero, seed, scaling,
                      tuple(s for s, _ in actions), (constant, linear, pairs))


def check():
    from random import Random
    from quadratic_image import multiply
    from quadratic_target import interpolate
    rng = Random(1543)
    def basis(k):
        cols = ()
        while len(cols) < k:
            cols = independent((*cols, rng.randrange(1 << k)))
        return cols

    checks = 0
    for m, modulus in ((1, 3), (2, 7), (3, 11)):
        for dim in (2, 4):
            n = m*dim
            for _ in range(2):
                ib, ob = basis(n), basis(m)
                mask = (1 << m) - 1
                shift, offset = rng.randrange(1 << n), rng.randrange(1 << m)
                def hidden(x):
                    x = apply_basis(ib, x ^ shift)
                    y = 0
                    for i in range(0, dim, 2):
                        a, b = (x >> (i*m)) & mask, (x >> ((i+1)*m)) & mask
                        y ^= multiply(a, b, modulus)
                    return apply_basis(ob, y) ^ offset
                chart = prepare(n, m, *interpolate(hidden, n))
                assert chart is not None
                data = [0] * (1 << m)
                for x in range(1 << n):
                    data[hidden(x)] += 1
                for t, expected in enumerate(data):
                    count, x = chart.solve(t)
                    assert count == expected and hidden(x) == t
                    checks += 1
    # Dual numbers and a product of two fields have full nondegenerate
    # bilinear multiplication. Frobenius and its fixed space distinguish them.
    def dual(x):
        a, b, c, d = [(x >> i) & 1 for i in range(4)]
        return (a*c) | ((a*d ^ b*c) << 1)
    def split(x):
        a, b, c, d = [(x >> i) & 1 for i in range(4)]
        return (a*c) | ((b*d) << 1)
    assert prepare(4, 2, *interpolate(dual, 4)) is None
    assert prepare(4, 2, *interpolate(split, 4)) is None
    def incompatible(x):
        a, b = x & 7, x >> 3
        square = multiply(a, a, 11)
        return multiply(a, b, 11) ^ multiply(square, square, 11)
    assert prepare(6, 3, *interpolate(incompatible, 6)) is None
    print(f"{checks} recoded field target counts/witnesses and three rejection controls passed")


if __name__ == "__main__":
    check()
