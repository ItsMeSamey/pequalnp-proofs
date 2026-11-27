from fractions import Fraction
from math import comb, factorial
from random import Random
from tapered_jet_machine import recover, inverse_odd
rng = Random(5107)
checks = 0
for a in range(1,5):
    L, alpha = 1<<a, 1<<(a+1)
    for u in range(1,a+1):
        m=u+1
        for p in (1,5,19):
            # Integer-valued binomial basis exercises nonintegral ordinary coefficients.
            polys = []
            for lane in range(3):
                poly = [Fraction(rng.randrange(-9,10))]
                basis = [Fraction(1)]
                for k in range(1,min(2*L,12)):
                    old = [Fraction(0)] + basis
                    for j, c in enumerate(basis): old[j] -= (k-1)*c
                    basis = [c/k for c in old]
                    poly.append(Fraction(0))
                    weight = rng.randrange(-5,6)
                    for j,c in enumerate(basis): poly[j] += weight*c
                polys.append(poly)
            def jet(t,j,d,pt):
                v = sum((c*comb(k,j)*t**(k-j)*alpha**j for k,c in enumerate(polys[d]) if k>=j),Fraction(0))
                assert v.denominator%2
                return v.numerator*inverse_odd(v.denominator,pt) + (rng.randrange(-5,6)<<pt)
            assert recover(a,u,m,p,3,jet)==[int(poly[0])%(1<<p) for poly in polys]
            checks+=1
print(checks, 'complete grids; three independent coordinates each')
