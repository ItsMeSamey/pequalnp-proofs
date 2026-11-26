from itertools import product
from random import Random
from solver import affine_chart,normalize,parity,quadratic,witness,zero_branches

def check_normal(M,eq):
    n = len(M)
    chart = affine_chart(n,eq)
    if chart is None:
        return 0
    points = [x for x in range(1<<n) if all(parity(x&m)==h for m,h in eq)]
    qs = [quadratic(M,x) for x in points]
    b,dirs,_ = chart
    affine = all(quadratic(M,b^u^v)^quadratic(M,b^u)^quadratic(M,b^v)^quadratic(M,b)==0 for u in dirs for v in dirs)
    for symmetric,possible in [(False,not any(qs)),(True,affine)]:
        A = normalize(M,eq,symmetric)
        assert (A is not None)==possible
        if A is not None:
            for i,row in enumerate(A):
                assert symmetric or not row>>i&1
                assert all((row>>j&1)==(A[j]>>i&1) for j in range(n))
            assert all(not x>>i&1 or parity((A[i]^M[i])&x)==0 for x in points for i in range(n))
    return 1

def check_witness(M,m,h):
    n = len(M)
    eq = [(m,h)]
    valid = [x for x in range(1<<n) if parity(x&m)==h and
             all(not x>>i&1 or not parity(row&x) for i,row in enumerate(M))]
    try:
        x = witness(M,m,h)
    except ValueError:
        return 0
    assert (x is not None)==bool(valid)
    assert x is None or x in valid
    return 1

def check_factor(n):
    base = list(range(1<<n))
    affine = {sum((parity(m&x)^h)<<x for x in base) for m in base for h in range(2)}
    pairs = {a&b for a in affine for b in affine}
    checked = 0
    for c in (0,1):
        # Adjoin a fixed variable to realize the constant, including n=0.
        for coeff in range(1 << (n*(n+1)//2)):
            M = [0]*(n+1)
            M[n] = c<<n
            bit = 0
            for i in range(n):
                for j in range(i+1):
                    M[i] |= ((coeff>>bit)&1)<<j
                    bit += 1
            table = sum(quadratic(M,x|1<<n)<<x for x in base)
            try:
                branches = zero_branches(M, affine_chart(n+1,[(1<<n,1)]))
            except ValueError:
                assert table not in pairs
            else:
                assert table in pairs
                for x in base:
                    assert any(parity(m&x)==h for m,h in branches) == (not (table>>x&1))
            checked += 1
    return checked

if __name__ == '__main__':
    rng = Random(821)
    factors = sum(check_factor(n) for n in range(5))
    normals = witnesses = 0
    for n in range(4):
        for M in product(range(1<<n),repeat=n):
            for m in range(1<<n):
                for h in (0,1):
                    normals += check_normal(M,[(m,h)])
                    witnesses += check_witness(M,m,h)
    for _ in range(800):
        n = rng.randrange(1,9)
        M = [rng.randrange(1<<n) for i in range(n)]
        eq = [(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(5))]
        normals += check_normal(M,eq)
        witnesses += check_witness(M,rng.randrange(1<<n),rng.randrange(2))
    print(factors,'factor checks;',normals,'consistent normalization checks;',witnesses,'covered witness checks')
