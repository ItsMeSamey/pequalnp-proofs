"""Finite-field audit of the local equality translation-rank bound."""
from itertools import product
from random import Random


def mul(a, b):
    c = 0
    while b:
        if b & 1:
            c ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 0b1011  # x^3+x+1
    return c


def inv(a):
    return next(b for b in range(1, 8) if mul(a, b) == 1)


def add(*items):
    out = 0
    for x in items:
        out ^= x
    return out


def conv(a,b):
    out = [0] * len(a)
    for s, x in enumerate(a):
        for t, y in enumerate(b):
            out[s ^ t] ^= mul(x, y)
    return out


def vector(n, pairs):
    vs = [0] * n
    for k, v in pairs:
        vs[k] ^= v
    return vs


def rank(rows):
    basis = {}
    for row in rows:
        row = row.copy()
        for k in range(len(row)):
            z = row[k]
            if not z:
                continue
            if k not in basis:
                basis[k] = [mul(x, inv(z)) for x in row]
                break
            row = [x ^ mul(z, y) for x, y in zip(row, basis[k])]
    return len(basis)


def translate(poly, s):
    # Coefficients in the squarefree monomial basis: expand X_m(X+s).
    out = [0] * len(poly)
    for m, coefficient in enumerate(poly):
        free = m & s
        j = free
        while True:
            out[m ^ j] ^= coefficient
            if not j:
                break
            j = (j - 1) & free
    return out


def evalpoly(poly, h):
    return add(*(v for m,v in enumerate(poly) if m & h == m))


def audit(rng, A, B, D, accepted, h, fixed=False):
    n = len(accepted)
    m = len(A)
    unit = [1] + [0] * (n-1)
    # In characteristic two the Boolean zeta transform is its own inverse.
    poly = [add(*(a for s,a in enumerate(accepted) if s & v == s)) for v in range(n)]
    translates = [translate(poly, s) for s in range(n)]
    assert [evalpoly(p,h) for p in translates] == [accepted[s^h] for s in range(n)]

    def weighted(support):
        return vector(n, ((s, (1 if fixed else rng.randrange(1,8))) for s in support))

    a = [weighted(s) for s in A]
    b = [weighted(s) for s in B]
    ds, dis = [], []
    for support in D:
        while True:
            # 0 is already the identity, so only nonzero elements get indeterminates.
            elem = vector(n, [(0, 1)] + [(s, rng.randrange(1,8)) for s in support if s])
            total = add(*elem)
            if total:
                break
        # D^2=(sum coefficients)^2 I, because every translation squares to I.
        invsquare = inv(mul(total, total))
        di = [mul(x,invsquare) for x in elem]
        assert conv(elem, di) == unit
        ds.append(elem)
        dis.append(di)

    def functional(vs):
        return add(*(mul(x, accepted[h ^ s]) for s, x in enumerate(vs)))

    full = unit
    for elem in ds:
        full = conv(full, elem)
    left = [conv(full, conv(x, z)) for x,z in zip(a,dis)]
    right = [conv(y, z) for y,z in zip(b,dis)]
    matrix = []
    for i in range(m):
        row = []
        for j in range(m):
            calc = functional(conv(left[i], right[j]))
            # Rank factorization in observable coordinates by independent evaluation.
            col = [add(*(mul(y,evalpoly(translates[s], h ^ r))
                         for s,y in enumerate(right[j]))) for r in range(n)]
            assert calc == add(*(mul(l,r) for l,r in zip(left[i],col)))
            if i != j:
                options = [A[i], B[j]] + [D[k] for k in range(m) if k not in (i,j)]
                factors = [a[i], b[j]] + [ds[k] for k in range(m) if k not in (i,j)]
                reachable = False
                scalar = 0
                for shifts in product(*options):
                    val = accepted[h ^ add(*shifts)]
                    reachable |= bool(val)
                    for op, shift in zip(factors, shifts):
                        val = mul(val, op[shift])
                    scalar ^= val
                assert calc == scalar and (not calc or reachable)
            row.append(calc)
        matrix.append(row)
    assert rank(matrix) <= n

    # Set all slack z variables to zero, then perturb one z_id by epsilon,
    # epsilon^2=0. Evaluate the whole expression on P over the dual numbers
    # as a chain of operators. Both denominator factors have same jet as D_i.
    for i, support in enumerate(D):
        for d in set(support) - {0}:
            constant = [accepted[h ^ x] for x in range(n)]
            linear = [0] * n
            for op in [a[i], b[i]]:
                constant = conv(constant, op)
                linear = conv(linear, op)
            for _ in range(3):  # D_i, D_i^-1, D_i^-1
                linear = [v ^ constant[r ^ d] for r, v in enumerate(linear)]
            target = add(*(mul(mul(a[i][x], b[i][y]), accepted[h ^ x ^ y ^ d])
                           for x, y in product(A[i], B[i])))
            assert linear[0] == target
    # Choose an actual C_i certificate under C_i ⊆ A_i+B_i+D_i and
    # fix the other D choices. One-hot A and B coefficients isolate its
    # formal monomial. Its diagonal constant/linear coefficient must be 1.
    for i in range(m):
        backgrounds = {add(*v) for v in product(*(D[k] for k in range(m) if k != i))}
        witnesses = {}
        for x,y,d in product(A[i],B[i],D[i]):
            witnesses.setdefault(x ^ y ^ d, (x,y,d))
        C = rng.sample(sorted(witnesses), rng.randint(0,len(witnesses)))
        for g in C:
            x,y,d = witnesses[g]
            for t in backgrounds:
                if not accepted[h ^ t ^ g]:
                    continue
                # The coefficient of all other chosen z_k is T_t. On the
                # i-th factor D_i^-1, take its constant or its linear z_id.
                shifted = translate(translate(translate(poly, t), x), y)
                coefficient = translate(shifted,d) if d else shifted
                assert evalpoly(coefficient,h) == 1
    return matrix


if __name__ == '__main__':
    rng = Random(983620)
    for trial in range(80):
        bdim = trial % 4
        n = 1 << bdim
        m = rng.randrange(1, 7)
        def randset():
            return sorted(rng.sample(range(n), rng.randint(1,min(3,n))))
        A, B = [[randset() for _ in range(m)] for _ in range(2)]
        D = [sorted({0, *randset()}) for _ in range(m)]
        audit(rng,A,B,D,[rng.randrange(2) for _ in range(n)], rng.randrange(n))
    # Local x-only and y-only labels match only on equal indices. Saturate rank.
    for n in (1,2,4,8):
        options = [[s] for s in range(n)]
        M = audit(rng, options, options, [[0]]*n, [1]+[0]*(n-1), 0, True)
        assert rank(M) == n
    # All equal index certificates require a *nonzero* D shift. Foreign indices
    # cannot match: their distinct high bits survive every slack choice.
    for n in (2,4,8):
        m = n//2
        M = audit(rng, [[2*j] for j in range(m)], [[2*j+1] for j in range(m)],
                  [[0,1]]*m, [1]+[0]*(n-1), 0, True)
        assert all(not M[i][j] for i in range(m) for j in range(m) if i != j)
    print('80 random GF(8) traces and 7 weighted-disjointness instances passed')
