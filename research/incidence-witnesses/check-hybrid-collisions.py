from fractions import Fraction as F

N, q, s = 161203, 401, 646424
for k, width in enumerate([78, 29, 17, 11, 8, 6, 5, 3, 2]):
    r = 2*k+1
    def bound(d):
        return ((1+F(d,2)+r*(d+1))*s + F(d,2)+r*(d-1)
                + (2*k*k+k-d-F(1,2))*N)
    assert bound(width) < N*q <= bound(width+1)
    print(k, width, N*q-bound(width))
assert N*q-(s+21*(3*s-4*N+3)+210*N) == 2959626
