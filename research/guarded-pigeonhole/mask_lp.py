"""Rational relaxation of binary guards and a parity marker.
Rows are affine expressions, with None denoting the constant term.
"""
from collections import Counter


def row(*terms):
    out = Counter()
    for coeff, var in terms:
        out[var] += coeff
    return {k: v for k, v in out.items() if v}


def bits(mask):
    return [i for i in range(mask.bit_length()) if mask & (1 << i)]


def x(i):
    return ('x', i)


def z(a):
    return ('z', a)


def relaxation(normals, offset, marker):
    n = len(normals)
    if any(a < 0 or a >= 1 << n for a in (*normals, offset, marker)):
        raise ValueError("mask outside pivot range")
    masks = {marker}
    ge, eq = {}, {}
    for i, a in enumerate(normals):
        other = a ^ (1 << i)
        masks.update((a, other))
        sign = 1 - 2 * ((offset >> i) & 1)
        eq['edge', i] = row((1,z(other)), (-1,z(a)), (-sign,x(i)))
        ge['xlo', i] = {x(i): 1}
        ge['xhi', i] = {None: 1, x(i): -1}
    for a in masks:
        ge['zlo', a] = {z(a): 1}
        ge['zhi', a] = {None: 1, z(a): -1}
        ge['support', a] = row(*[(1,x(i)) for i in bits(a)], (-1,z(a)))
        if a.bit_count() == 1:
            eq['unit', a] = {z(a): 1, x(a.bit_length() - 1): -1}
    eq['marker', marker] = {z(marker): 1, None: -1}
    return ge, eq


def compiler(holes, others):
    """Pigeon p<h is matched to hole p. Others lists the nonmatching edges."""
    n = len(others)
    pivots = [[i for i, (p, _) in enumerate(others) if p == u] for u in range(holes+1)]
    normals = [None] * n
    ends = []
    for h in range(holes):
        start = sum(1 << i for i in pivots[h])
        current = start
        for i, (_, v) in enumerate(others):
            if v == h:
                normals[i] = current
                current ^= 1 << i
        ends.append((start, current))
    return normals, (1 << n)-1, sum(1 << i for i in pivots[-1]), ends


def certificate(holes, others):
    normals, offset, marker, ends = compiler(holes, others)
    ge, eq = relaxation(normals, offset, marker)
    total = Counter()
    for start, end in ends:
        if start == end:
            for i in bits(start):
                total.update(ge['xlo', i])
        else:
            total.update(ge['support', start])
            total.update(ge['zlo', end])
    total.update(ge['support', marker])
    total.update(eq['marker', marker])
    for i in range(len(normals)):
        total.subtract(eq['edge', i])
    assert {k: v for k, v in total.items() if v} == {None: -1}


def cycle_counterexample():
    from fractions import Fraction
    n = 4
    normals = [(1 << ((i-1) % n)) | (1 << ((i+1) % n)) for i in range(n)]
    full = (1 << n)-1
    ge, eq = relaxation(normals, full, full)
    assignment = {None: 1, z(full): 1}
    for i, a in enumerate(normals):
        assignment[x(i)] = Fraction(1, 2)
        assignment[z(a)] = 1
        assignment[z(a ^ (1 << i))] = Fraction(1, 2)
    def ev(q):
        return sum(v * assignment[k] for k, v in q.items())
    assert all(ev(r) >= 0 for r in ge.values())
    assert all(ev(r) == 0 for r in eq.values())
    assert not any(t.bit_count() % 2 and all(not t & (1 << i) or (t & a).bit_count() % 2
                    for i, a in enumerate(normals)) for t in range(1 << n))


if __name__ == '__main__':
    h = 3
    optional = [(p, v) for p in range(h+1) for v in range(h) if p != v]
    for mask in range(1 << len(optional)):
        certificate(h, [edge for i, edge in enumerate(optional) if mask & (1 << i)])
    cycle_counterexample()
    print('512 exact LP contradiction certificates and the rational four-cycle example passed.')
