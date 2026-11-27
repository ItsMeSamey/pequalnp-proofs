from fractions import Fraction as F
from math import prod

def K(t):
    if t<=8:
        return 2+F(t+1,6*t-3)*(54+2*F(t+4,t-2)+2*F(8-t,t-1))
    return 2+(54+F(24,t-2))/5

c=2/K(13)
assert c==F(55,364)
assert all(K(j)>K(j+1) and K(j)>j+1 for j in range(3,13))
nfinal=(2-13*c)*prod((K(j)-j)/(K(j)-j-1) for j in range(3,13))
assert nfinal>F(105,100)
assert 14*c>1
print(c,float(nfinal))
