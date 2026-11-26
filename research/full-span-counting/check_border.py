"""Check the Boolean border certificate and correction using positive moments."""
from collections import defaultdict
from fractions import Fraction as F
from random import Random
from sympy import Matrix


def combine(*terms):
    out = defaultdict(F)
    for scale, poly in terms:
        for mask, coeff in poly.items():
            out[mask] += scale * coeff
    return {key: v for key, v in out.items() if v}


def mul(a, b):
    out = defaultdict(F)
    for u, c in a.items():
        for v, d in b.items():
            out[u | v] += c*d
    return {key: v for key, v in out.items() if v}


def value(poly, u):
    return sum(c for mask, c in poly.items() if mask & u == mask)


ONE = {0: F(1)}


def build(m, points):
    if not points:
        return ONE, {}, 0
    pivots = {}
    basis = []
    def add(mask):
        v = [F(int(mask & u == mask)) for u in points]
        for idx, b in sorted(pivots.items()):
            a = v[idx]
            v = [e-a*d for e, d in zip(v, b)]
        idx = next((i for i, x in enumerate(v) if x), None)
        if idx is not None:
            pivots[idx] = [x/v[idx] for x in v]
            basis.append(mask)
    add(0)
    for mask in basis:  # Appended independent monomials also enter the closure.
        for i in range(m):
            add(mask | (1 << i))
    assert len(basis) == len(points)
    inv = Matrix([[int(a & u == a) for a in basis] for u in points]).inv()
    def interpolate(y):
        coeffs = inv * Matrix(y)
        return {mask: F(c) for mask, c in zip(basis, coeffs) if c}
    cert = {}
    for mask in basis:
        for i in range(m):
            a = mask | (1 << i)
            image = interpolate([int(a & u == a) for u in points])
            r = combine((1, {a: F(1)}), (-1, image))
            cert = combine((1, cert), (1, mul(r, r)))
    h = interpolate([F(1, u.bit_count()) if u else 0 for u in points])
    return cert, h, len(basis)


def indicator(m, u):
    poly = ONE
    for i in range(m):
        x = {1 << i: F(1)}
        poly = mul(poly, x if u >> i & 1 else combine((1, ONE), (-1, x)))
    return poly


def check(m, excluded, rng):
    full = range(1 << m)
    weight = [rng.randrange(6) for _ in full]
    cert, h, e = build(m, excluded)
    assert len(cert) <= max(1, m*e*(e+1)**2)
    assert all((value(cert, u) == 0 if u in excluded else value(cert, u) > 0)
               for u in full)
    # Construct an oracle predictor with arbitrary signed rational errors on E.
    f = combine((1, ONE), (-1, indicator(m, 0)))
    for u in excluded:
        if u:
            f = combine((1, f), (F(rng.choice([-3, -1, 2]), 3), indicator(m, u)))
    q = {1 << i: F(1) for i in range(m)}
    delta = combine((1, ONE), (-1, f))
    correction = mul(mul(q, delta), h)
    positive_moments = {a: sum(weight[u] for u in full if u & a == a) for a in full}
    def count(poly):
        return sum(c * positive_moments[a] for a, c in poly.items())
    assert sum(weight)-count(f)-count(correction) == weight[0]
    assert count(mul(cert, mul(q, mul(delta, delta)))) == 0
    probe = {1 << i: F(rng.randint(-2, 2), 2) for i in range(m)}
    loss = mul(q, mul(probe, probe))
    assert (count(mul(cert, loss)) > 0) == any(
        weight[u] and u not in excluded and value(loss, u) for u in full)


def main():
    rng = Random(38171)
    cases = 0
    for m in range(4):
        for inclusion in range(1 << (1 << m)):
            check(m, [u for u in range(1 << m) if inclusion >> u & 1], rng)
            cases += 1
    for m in (4, 5, 6):
        for _ in range(12):
            check(m, rng.sample(range(1 << m), rng.randrange(1, 9)), rng)
            cases += 1
    print(f"{cases} exact cases passed, including every excluded subset of every "
          "Boolean cube through dimension 3.")


if __name__ == '__main__':
    main()
