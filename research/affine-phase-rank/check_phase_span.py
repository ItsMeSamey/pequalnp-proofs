from itertools import product
from random import Random
from sympy import Matrix, Poly, symbols
rng=Random(273)
x=symbols("x")
tested=0
for n in range(1,6):
    for coeff in product(range(4),repeat=n):
        for vals in product(range(2),repeat=n):
            a=sum(c*z for c,z in zip(coeff,vals))
            lows=[(c&1)*z for c,z in zip(coeff,vals)]
            high=(sum((c>>1)*z for c,z in zip(coeff,vals))+sum(lows[i]*lows[j] for i in range(n) for j in range(i)))%2
            assert a%4 == (sum(lows)%2)+2*high
            tested+=1
for _ in range(80):
    scores=[rng.randint(-3,3) for _ in range(rng.randint(3,24))]
    h=len(set(scores))
    mu=[sum(b**i for b in scores) for i in range(2*h+1)]
    M=Matrix(h+1,h+1,lambda i,j:mu[i+j])
    v,=M.nullspace()
    assert M.rank()==h and v[h]!=0
    polynomial=Poly(sum(c*x**i for i,c in enumerate(v/v[h])),x)
    assert set(polynomial.ground_roots())==set(scores)
print(f"{tested} modulo-four phase splits and 80 realized-score recoveries passed")
