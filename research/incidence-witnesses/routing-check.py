for q in range(289,377):
    n=q*q+q+1
    d=q*q-20*q
    def g(x):
        return q*x//(q*q-x)
    assert n-d>g(d)+1
    u=(q*d+2*(q-1)*(n-d))//((q-1)**2-d)
    h0=d-u
    assert 0<=h0<=d and q**3<=(q*q-d)**2
    s=2*n+2*d-1-u-g(d)-g(h0)
    assert 100*s>=n*q
    print(q,s,(n*q+99)//100)
q=377
n=q*q+q+1
d=134173
assert n-d>g(d)+1
u=(q*d+2*(q-1)*(n-d))//((q-1)**2-d)
def lower(h):
    excess=max(0,d-h-u,(n-h-u+1)//2)
    return 2*n+d+h-1-g(d)-g(h)+excess
s=min(lower(h) for h in range(d+1))
assert 100*s>=n*q
print(q,s,(n*q+99)//100)
from fractions import Fraction
q=378
n=q*q+q+1
d=q*q-19*q
r=n-d
assert r>g(d)+1
wc=[]
for w,alpha in [(1,Fraction(4,65)),(2,Fraction(2,35))]:
    for k in range(q+2):
        Q=Fraction((w+1)*(k-20)*(k-21),420)
        c=k-1 if k>=3 else 0
        assert Q>=w*(k<=1)
        assert Q+alpha*c>=1+w*(k==0)
    cost=alpha*r+Fraction((w+1)*(q*r+r*r-41*(q+1)*r+420*n),420)
    wc.append(cost.numerator//cost.denominator)
s=min(2*n+d-1-g(h)+max(d-wc[0],(n+h-wc[1]+1)//2) for h in range(d+1))
assert 100*s>=n*q
print(q,s,(n*q+99)//100)
