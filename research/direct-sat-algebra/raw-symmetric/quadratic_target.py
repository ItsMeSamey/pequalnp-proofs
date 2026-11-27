"""Exact target counting after affine restriction and common-polar-radical descent.

Bit-packed input/output conventions match quadratic_image. Equations are (mask,
rhs) parity equations. prepare returns None if linear algebra rules out target.
Otherwise the quotient input can be submitted to a separate budgeted target
probe; lifting a witness just solves a tracked linear equation. solve caps the
field size for full quotient image discovery; budget exhaustion is inconclusive.
"""
from dataclasses import dataclass
from itertools import combinations
from random import Random
from quadratic_image import (FieldBudgetExceeded, Quadratic, bits, discover,
                             normalize, parity)

TargetBudgetExceeded = FieldBudgetExceeded


def reduce_vector(value, rows):
    preimage = 0
    for pivot in sorted(rows, reverse=True):
        if value >> pivot & 1:
            row, source = rows[pivot]
            value ^= row
            preimage ^= source
    return value, preimage


def insert(value, source, rows):
    residue, adjustment = reduce_vector(value, rows)
    if residue:
        rows[residue.bit_length() - 1] = residue, source ^ adjustment
    return residue


def affine_domain(n, equations):
    rows = {}
    for row, rhs in equations:
        if row < 0 or row >= 1 << n or rhs not in (0, 1):
            raise ValueError("invalid affine equation")
        r, b = reduce_vector(row, rows)
        if r:
            rows[r.bit_length() - 1] = r, rhs ^ b
        elif rhs ^ b:
            return None

    def substitute(x, homogeneous):
        for i in sorted(rows):
            row, b = rows[i]
            x |= (parity(row & x) ^ (0 if homogeneous else b)) << i
        return x

    return (substitute(0, False), [substitute(1 << i, True)
                                   for i in range(n) if i not in rows],
            sorted(rows))


def apply_basis(basis, mask):
    x = 0
    for i in bits(mask):
        x ^= basis[i]
    return x


def interpolate(evaluate, n):
    """Packed vector ANF via values at points of Hamming weight at most two."""
    c = evaluate(0)
    linear = [evaluate(1 << i) ^ c for i in range(n)]
    pairs = {}
    for i, j in combinations(range(n), 2):
        v = evaluate((1 << i) | (1 << j)) ^ c ^ linear[i] ^ linear[j]
        if v:
            pairs[i, j] = v
    return c, linear, pairs


def evaluate_anf(c, linear, pairs, x):
    y = c ^ apply_basis(linear, x)
    for (i, j), v in pairs.items():
        if (x >> i) & (x >> j) & 1:
            y ^= v
    return y


@dataclass
class TargetReduction:
    n: int
    forms: tuple
    target: int
    multiplicity: int
    lift: object


def prepare(n, forms, target, equations=()):
    forms = tuple(forms)
    if n < 0 or not 0 <= target < 1 << len(forms):
        raise ValueError("invalid dimension or target")
    normalized = [normalize(n, f) for f in forms]
    domain = affine_domain(n, equations)
    if domain is None:
        return None
    offset, basis, _ = domain
    d = len(basis)

    def original(x):
        y = 0
        for j, (c, linear, pairs) in enumerate(normalized):
            bit = c ^ parity(linear & x)
            for u, v in pairs:
                bit ^= (x >> u) & (x >> v) & 1
            y |= bit << j
        return y

    c, linear, pairs = interpolate(lambda z: original(offset ^ apply_basis(basis, z)), d)
    polar = {}
    for (i, j), coeff in pairs.items():
        for bit in bits(coeff):
            polar[bit, i] = polar.get((bit, i), 0) ^ (1 << j)
            polar[bit, j] = polar.get((bit, j), 0) ^ (1 << i)
    _, radical, pivots = affine_domain(d, ((v, 0) for v in polar.values()))
    complement = [1 << i for i in pivots]
    image_rows = {}
    for r in radical:
        # The directional derivative is constant on the whole domain.
        insert(evaluate_anf(0, linear, pairs, r), r, image_rows)
    multiplicity = 1 << (len(radical) - len(image_rows))

    def residual(y):
        return reduce_vector(y, image_rows)[0]

    # Complement is a coordinate subspace in the restricted input coordinates.
    qlin = [residual(linear[i]) for i in pivots]
    qpair = {(i, j): residual(pairs.get((pivots[i], pivots[j]), 0))
             for i, j in combinations(range(len(pivots)), 2)}
    # Compress the affine hull of the quotient image by linear coordinates.
    hull = {}
    for v in (*qlin, *qpair.values()):
        insert(v, 0, hull)
    goal = residual(target ^ c)
    if reduce_vector(goal, hull)[0]:
        return None
    # Echelon pivot coordinates inject on the span, even without reduced rows.
    coords = sorted(hull)
    quotient = tuple(Quadratic(0, sum(((v >> b) & 1) << i for i, v in enumerate(qlin)),
                               tuple(pair for pair, v in qpair.items() if v >> b & 1))
                     for b in coords)
    packed_goal = sum(((goal >> b) & 1) << j for j, b in enumerate(coords))

    def lift(u):
        if not 0 <= u < 1 << len(pivots):
            raise ValueError("quotient witness out of range")
        z = apply_basis(complement, u)
        delta = target ^ evaluate_anf(c, linear, pairs, z)
        left, r = reduce_vector(delta, image_rows)
        if left:
            raise ValueError("quotient witness misses target")
        return offset ^ apply_basis(basis, z ^ r)

    return TargetReduction(len(pivots), quotient, packed_goal, multiplicity, lift)


def solve(n, forms, target, equations=(), *, max_field_size=64):
    if not isinstance(max_field_size, int) or max_field_size < 2:
        raise ValueError("max_field_size must be an integer >= 2")
    red = prepare(n, forms, target, equations)
    if red is None:
        return 0, None
    if not red.forms:
        return (1 << red.n) * red.multiplicity, red.lift(0)
    image = discover(red.n, red.forms, max_field_size=max_field_size)
    if red.target not in image:
        return 0, None
    count, u = image[red.target]
    return count * red.multiplicity, red.lift(u)


def check():
    from quadratic_image import evaluate
    rng = Random(438354)
    count = 0
    for _ in range(70):
        n, m = rng.randrange(6), rng.randrange(5)
        forms = [Quadratic(rng.randrange(2), rng.randrange(1 << n),
                           tuple(p for p in combinations(range(n), 2)
                                 if rng.randrange(2))) for _ in range(m)]
        eq = [(rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(4))]
        for target in range(1 << m):
            models = [x for x in range(1 << n) if evaluate(forms, x) == target
                      and all(parity(a & x) == b for a, b in eq)]
            value, witness = solve(n, forms, target, eq, max_field_size=512)
            assert value == len(models) and (witness in models if models else witness is None)
            count += 1
    n = 48
    affine = [Quadratic(0, 1 << i) for i in range(n)]
    assert solve(n, affine, (1 << n) - 1) == (1, (1 << n) - 1)
    pairs = tuple(combinations(range(8), 2))
    dense = [Quadratic(0, 0, pairs)] * 25
    result = solve(8, dense, (1 << 25) - 1)
    assert result[0] == sum(evaluate(dense, x) != 0 for x in range(256))
    assert evaluate(dense, result[1]) == (1 << 25) - 1
    # Each triangle form has derivative one on the all-ones direction.
    # A dense invertible triangular change of output coordinates preserves
    # the 2^20 output image with equal fibers and gives only pure quadratics.
    triangles = [tuple(combinations(range(3*i, 3*i+3), 2)) for i in range(20)]
    pure = [Quadratic(0, 0, sum(triangles[:i+1], ())) for i in range(20)]
    target = 0x5a5a5
    reduced = prepare(60, pure, target)
    assert len(reduced.forms) == 0 and reduced.n == 40
    exact, model = solve(60, pure, target, max_field_size=2)
    assert exact == 1 << 40 and evaluate(pure, model) == target
    hostile = [Quadratic(0, 0, ((2*i, 2*i+1),)) for i in range(16)]
    try:
        solve(32, hostile, 0, max_field_size=2)
    except TargetBudgetExceeded:
        pass
    else:
        raise AssertionError("hostile quotient bypassed the field cap")
    print(f"{count} restricted target checks and four structured controls passed")


if __name__ == "__main__":
    check()
