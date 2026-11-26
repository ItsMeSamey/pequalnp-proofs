"""Check integer idempotent digits and coherent Tanner witness-face jets."""
from itertools import product
from math import comb
from sympy import Poly, symbols

y = symbols('y')
h = Poly(y*y-y,y)


def digits(ell):
    value = Poly((1-y)**ell*sum(comb(ell+j-1,j)*y**j for j in range(ell)),y)
    initial = value
    pieces = []
    for j in range(ell):
        value, digit = divmod(value,h)
        pieces.append(digit)
    assert value.is_zero and sum((a*h**j for j,a in enumerate(pieces)),Poly(0,y))==initial
    return pieces


if __name__=='__main__':
    for ell in range(1,9):
        e = digits(ell)
        assert e[0]==Poly(1-y,y)
        for v in range(-8,9):
            lift = [d.eval(v)*(v*(v-1))**j for j,d in enumerate(e)]
            assert sum(lift)%2**ell == int(v%2==0)
            if v==0:
                assert lift==[1]+[0]*(ell-1)
    z = Poly(y,y)
    one = Poly(1,y)
    for a,s,x,u in product(range(4),repeat=4):
        value = one
        for i in range(2):
            first = ((a>>i)&1) + ((x>>i)&1)
            second = ((s>>i)&1) - z*((u>>i)&1)
            value *= (one-(one+z)*first)*(one-(one+z)*second)
        j = s.bit_count()
        assert all(value.nth(k)==0 for k in range(j))
        predicted = (-1)**(a.bit_count()+j)*int(a==x and not(s&u))
        assert value.nth(j)==predicted
    print('8 integer lift decompositions, 136 integer evaluations, 256 two-pair coherent face tests passed')
