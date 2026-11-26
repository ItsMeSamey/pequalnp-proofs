from fractions import Fraction as F
from math import comb
N=161203
L=646425
p=F(15,16)
k=19
mass=[comb(402,i)*(1-p)**i*p**(402-i) for i in range(k)]
short=sum((k-i)*mass[i] for i in range(k))
bad=2*N*(mass[0]+mass[1])
hurdle=L-4*N+2*N*(1-p)*(2+short)/(k+1)+4*N*bad+1+2*N*p**403
assert hurdle<F(3863701,1000)
for j,m in [(2,4397),(8,6475)]:
    assert (m-1)*p**j<=hurdle<m*p**j
print(float(hurdle),'and both shared-gate thresholds passed')
for h,extra,expected in [(399,3216,[(2,3249),(8,3350),(50,4285),(100,6416)]),
                          (400,2950,[(2,2965),(8,3011),(50,3371),(100,3931),(300,11713)])]:
    d=h*402+1
    n=2*(N-d)
    k=402-h
    assert L-(2*n-1-2*n//(k+1))-4*d+2*h == extra
    for w,m in expected:
        chance=1-F(w*(N-d),N)
        assert (m-1)*chance<extra<=m*chance
print('Dense balanced flag thresholds passed')
