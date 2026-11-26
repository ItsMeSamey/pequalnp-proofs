"""Exhaustive small checks of dense flips and the one-query decoding reduction."""
from itertools import combinations, product

def span(rows):
    s = {0}
    for row in rows:
        s |= {v ^ row for v in s}
    return s

def flip_check():
    n = 3
    monomials = [sum(1 << i for i in subset)
                 for degree in range(3) for subset in combinations(range(n),degree)]
    for terms in range(1 << len(monomials)):
        roots = set()
        for x in range(1 << n):
            q = sum(1 for j,m in enumerate(monomials) if terms >> j & 1 and x & m == m)
            if q % 2 == 0:
                roots.add(x)
        for costs in product((-2, 0, 1), repeat=n):
            u = sum(1 << i for i,c in enumerate(costs) if c > 0)
            def opt(domain):
                return max((sum(c for i,c in enumerate(costs) if x >> i & 1)
                            for x in domain), default=None)
            assert opt(roots) == opt(x for x in roots if (x ^ u).bit_count() <= 2)

def hits(h, marginals, den):
    if not h:
        return False
    scope = [i for i in range(len(marginals)) if h >> i & 1]
    for s in range(1, 1 << len(scope)):
        if s.bit_count() % 2 == 0:
            continue
        mismatch = sum(den-marginals[i] if s >> j & 1 else marginals[i]
                       for j,i in enumerate(scope))
        if mismatch < den:
            return True
    return False

def decoding_check():
    n = 3
    codes = {frozenset(span(rows)) for size in range(n+1)
             for rows in combinations(range(1 << n), size)}
    assert len(codes) == 16
    for code in codes:
        for v in range(1 << n):
            for k in (1,2,3):
                den = 2*k + 1
                marginals = [den] + [1]*(2*n)
                checks = {b | (d << 1) | (d << (1+n))
                          for b in (0,1) for c in code for d in [c ^ (b*v)]}
                assert any(hits(h,marginals,den) for h in checks) == any(
                    (c^v).bit_count() <= k for c in code)
    return len(codes)

if __name__ == '__main__':
    flip_check()
    print('All three-bit quadratics passed. Decoding subspaces checked:', decoding_check())
