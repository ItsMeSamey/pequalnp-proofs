"""Check the two-column residue constraints independently modulo a prime."""
from fractions import Fraction
from math import factorial, prod

P = 1_000_000_007


def residue(t, r):
    return prod(Fraction(2*(i-r)-1, (i-r)*(i-r-1))
                for i in range(t) if i not in (r, r+1))


def determinant_mod(matrix):
    a = [row[:] for row in matrix]
    ans = 1
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i] % P), None)
        if pivot is None:
            return 0
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            ans = -ans
        z = a[i][i] % P
        ans = ans*z % P
        inv = pow(z, -1, P)
        for row in a[i+1:]:
            f = row[i]*inv % P
            for j in range(i, len(a)):
                row[j] = (row[j]-f*a[i][j]) % P
    return ans % P


def matrix(length, t):
    weights = [residue(t,r)*(-1)**r for r in range(t-1)]
    assert all(w>0 for w in weights)
    weights = [w.numerator*pow(w.denominator,-1,P)%P for w in weights]
    def entry(p,j):
        return sum(w*factorial(length-1+p-r)*factorial(length-1-p+r)
                   *(p-r)**j for r,w in enumerate(weights)) % P
    return [[entry(p,j) for j in range(t-1)] for p in range(t-1)]


if __name__ == '__main__':
    for length in (2,4,8,16,32):
        dets=[determinant_mod(matrix(length,t)) for t in range(2,length+1)]
        assert all(dets)
        print(length,len(dets),dets[-1])
