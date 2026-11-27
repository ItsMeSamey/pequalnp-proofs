from random import Random
from itertools import product
from one_defect_triangle import solve,product_matrix
from quadratic_target import affine_domain,apply_basis,parity


def check(n,H,checks,t):
    w,stats=solve(n,H,checks,t)
    good={x for x in range(1<<n) if all(not(x>>(a//2)&1==a%2 and x>>(b//2)&1==b%2) for a,b in H)
          and sum(parity(x&r)<<j for j,r in enumerate(checks))==t}
    assert w in good if good else w is None
    return w,stats


if __name__=='__main__':
    rng=Random(44)
    for _ in range(120):
        k=rng.randrange(1,34)
        A=[[rng.randrange(-4,5) for i in range(k)] for j in range(5)]
        B=[[rng.randrange(-4,5) for j in range(3)] for i in range(k)]
        assert product_matrix(A,B)==[[sum(x*y for x,y in zip(a,b)) for b in zip(*B)] for a in A]
    H=[(2*i+1,6) for i in range(3)]
    # Three singleton choices all force bit 3. Three independent checks force all choices.
    w,s=check(4,H,[1,2,4,8],15)
    assert w==15 and s['large']>=1
    for _ in range(500):
        n=rng.randrange(1,7)
        H=[(rng.randrange(2*n),rng.randrange(2*n)) for i in range(rng.randrange(2*n+1))]
        checks=[rng.randrange(1<<n) for j in range(rng.randrange(4))]
        check(n,H,checks,rng.randrange(1<<len(checks)))
    # Original source embedded with z data, plus a coordinate per G row.
    for _ in range(70):
        n=rng.randrange(1,4)
        rows=[rng.randrange(1<<n) for _ in range(n)]
        beta=rng.randrange(1,1<<n)
        H=[(2*i+1,2*(n+i)+1) for i in range(n)]
        checks=[beta]+[r^(1<<(n+i)) for i,r in enumerate(rows)]
        w,s=check(2*n,H,checks,1)
        if w is not None:
            z=w% (1<<n)
            assert parity(z&beta) and all(not(z>>i&1 and parity(z&r)) for i,r in enumerate(rows))
    print('120 signed products, triple overlap, 500 auxiliary and 70 original cases passed')
