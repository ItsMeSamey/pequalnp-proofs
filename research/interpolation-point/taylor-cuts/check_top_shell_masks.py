from fractions import Fraction
from itertools import product
from math import prod
L,t,alpha,h=16,2,32,9
T=t+alpha
grid=range(-L,L)
c0=Fraction(prod(T-s for s in grid),prod(-s for s in grid if s))
def mask(v):
    assert v.denominator%2
    return v.numerator%2
checks=nonzero=0
for X in product(range(2),repeat=4):
    src=[X[0]^X[2],X[2]]
    for Y in product(range(2),repeat=2):
        for base in (1,4):
            full=[[],[]]; tags=[[],[]]
            for r,x in enumerate((0,4)):
                local=sum(c0*X[k]/(T-y+x) for k,y in [(1,2),(3,6)])
                sign=1 if Y[r] else -1
                intercept=(1-Y[r])+sign*local
                full[r].append((0,intercept)); tags[r].append((0,mask(intercept)))
                for b in range(h-base):
                    coeff=c0/(T+x)*Fraction(4,T+x)**b
                    w=base+b
                    moment=sum(j**b*X[2*j] for j in range(2))
                    full[r].append((w,sign*coeff*moment))
                    tags[r].append((w,mask(sign*coeff/2**w)*src[int(b>0)]))
            exact=sum(prod(v for _,v in row) for row in product(*full) if sum(k for k,_ in row)==h-1)
            batched=sum(prod(v for _,v in row) for row in product(*tags) if sum(k for k,_ in row)==h-1)%2
            assert mask(exact/Fraction(2**(h-1)))==batched
            if base==1: assert batched==0
            else: nonzero+=batched
            checks+=1
assert nonzero
print(checks,'checks,',nonzero,'nonzero tightened cases')
