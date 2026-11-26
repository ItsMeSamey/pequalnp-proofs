from fractions import Fraction
from math import factorial, prod, ceil, floor


def valuation(x):
    if x == 0:
        return 10**6
    x = Fraction(x)
    return ((x.numerator & -x.numerator).bit_length()
            - (x.denominator & -x.denominator).bit_length())


def check(a, u, d):
    s = sum(Fraction(u-i, 2**i) for i in range(u))
    alpha = 2**(a+1)
    for up in (True, False):
        scale = Fraction(d+up, s)
        counts = [(ceil if up else floor)(scale*(u-i)/2**i) for i in range(u)]
        points = [2**i*(2*r+1) for i,n in enumerate(counts) for r in range(n)]
        if up:
            for x in points:
                i = valuation(x)
                r = ((x >> i)-1)//2
                n = counts[i]
                w = prod(Fraction(-y, x-y) for y in points if y != x)
                assert -valuation(w) == n-1+valuation(factorial(r)*factorial(n-r-1))-sum((l-i)*counts[l] for l in range(i+1,u))
                assert -valuation(w) <= 6*scale/2**i
        else:
            for t in range(-alpha//2, alpha//2):
                coeffs = [Fraction(1)]
                for x in points:
                    c, m = Fraction(x-t,x), Fraction(-alpha,x)
                    coeffs = [c*b+m*v for b,v in zip(coeffs+[0],[0]+coeffs)]
                i = valuation(t)
                predicted = 0
                if i < u:
                    b = ((t >> i)-1)//2
                    predicted = counts[i]+sum((b-r) % 2**j == 0 for j in range(1,a-i+1) for r in range(counts[i]))-sum((l-i)*counts[l] for l in range(i+1,u))
                assert min(map(valuation,coeffs)) == predicted


if __name__ == '__main__':
    for a,u in [(2,1),(4,2),(6,3)]:
        for d in [1,3,7,14,25]:
            check(a,u,d)
    print('15 tapered weight and polynomial-content fixtures passed')
