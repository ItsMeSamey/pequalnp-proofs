from fractions import Fraction

for q in range(289, 323):
    N = q*q + q + 1
    d = q*q - 26*q
    V = 2*N - d
    def f(a):
        return Fraction(q*a + 2*(q-1)*(N-a), (q-1)**2-a)
    max_u = int(f(0) + f(d))
    cheap = q*d // (q*q - d)
    excess = (V-max_u+1)//3
    lower = 2*N+d-1-cheap+excess
    assert lower*100 >= N*q
    if q >= 320:
        print(q, d, max_u, lower, (N*q+99)//100)
