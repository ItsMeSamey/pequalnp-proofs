from fractions import Fraction as F
s=646424
N=161203
for w,M,t in [(8,3010,48),(2,2964,62)]:
    D=w*M
    I=max(M,D-M)
    A=s-I+t
    C=F(A,8)+1206*t
    assert 402-C//804>=200
    assert 200*(N-D-C)>1
    print(w,'remaining units',float(N-D-C))
