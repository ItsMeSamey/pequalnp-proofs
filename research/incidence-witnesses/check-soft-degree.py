from fractions import Fraction
from math import comb

N, L, d = 161203, 646425, 402
def hurdle(k):
    shortfall = Fraction(sum((k-i)*comb(d,i) for i in range(k)), 2**d)
    return L-4*N+N*(2+shortfall)/(k+1)

rare = Fraction(8*N*N*(d+1), 2**d)
sole = Fraction(2*N, 2**403)
root = Fraction(1,2**100)
best = min(range(2,d+1), key=hurdle)
bound = hurdle(best)+rare+sole+root
print(best, float(bound))
assert best == 178 and bound < Fraction(3447324,1000)
