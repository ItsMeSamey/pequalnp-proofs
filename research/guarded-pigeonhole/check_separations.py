"""Check exact-rational feasibility against the research mask LP on planted graphs."""
from fractions import Fraction
from mask_lp import bits, compiler, relaxation


def check_values(normals, marker, choose):
    ge, eq = relaxation(normals, (1 << len(normals))-1, marker)
    def value(row):
        return sum(coeff * (1 if key is None else choose(*key)) for key, coeff in row.items())
    assert all(value(row) >= 0 for row in ge.values())
    assert all(value(row) == 0 for row in eq.values())


def check_graph(others):
    R, _, L, _ = compiler(3, others)
    if L.bit_count() < 2:
        return False
    n = len(R)
    e = bits(L)[0]
    unit = 1 << e
    t = 1 << n
    y = [(2 << n) << i for i in range(4)]
    Y = sum(y)
    cycle = [y[(i-1)%4] | y[(i+1)%4] for i in range(4)]
    R1 = R[:]
    R1[e] ^= t
    R1 += [Y] + cycle
    half = Fraction(1, 2)
    def asymmetric(kind, m):
        if kind == 'x':
            return half if (1 << m) & Y else int(bool((1 << m) & (t | unit)))
        if m & Y:
            if m == Y | t:
                return 0
            return half if m.bit_count() == 3 else 1
        return ((t | unit) & m).bit_count() % 2
    check_values(R1, L, asymmetric)

    RR = R[:] + [a << n for a in R]
    RR[e] ^= L << n
    RR[n+e] ^= L
    LL = L | (L << n)
    ht = unit | (unit << n)
    assert LL not in set(RR) | {a ^ (1 << i) for i, a in enumerate(RR)}
    def symmetric(kind, m):
        if kind == 'x':
            return half if ht & (1 << m) else 0
        if m == LL:
            return 1
        return half * ((ht & m).bit_count() % 2)
    check_values(RR, LL, symmetric)
    return True


if __name__ == '__main__':
    allowed = [(p, h) for p in range(4) for h in range(3) if p != h]
    count = sum(check_graph([edge for i,edge in enumerate(allowed) if pattern >> i & 1])
                for pattern in range(1 << len(allowed)))
    assert count == 256
    print(f'Both LP assignments passed on {count} planted graphs with unmatched degree at least two.')
