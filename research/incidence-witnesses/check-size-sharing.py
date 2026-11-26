from fractions import Fraction as F
s=646424
N=161203
for ell in range(2,s+2):
    b8=ell+8*1206
    j=b8//(8*804)
    assert 1<=j<402 and 8*804*j<=b8 and 8*ell<=b8*(j+2)
for t in range(67):
    c=F(s+t,8)+1206*t
    assert 402-c//804>=203 and 203*(N-c)>1
assert 804*40*(s+40)<144189**2
print('All cone sizes and 67 shared-slot threshold passed')
