"""Check valuation identities with exact integer arithmetic on small grids."""
from fractions import Fraction
from itertools import combinations, product
from math import factorial, prod

def val(x):
    x=abs(x)
    return (x & -x).bit_length()-1

def retained_loss(a, i, q):
    return sum(Fraction(j*(q[i]-q[i+j]),2**j) for j in range(1,a-i+1))

def check_losses():
    checks=0
    for u in range(1,5):
        a=2*u
        for head in product(range(4), repeat=u):
            if not any(head):
                continue
            q=list(head)+[0]*(a+1-u)
            S=[j for j in range(-2**a,2**a) if j]
            for i in range(u):
                if not q[i]:
                    continue
                t=2**i
                actual=sum(q[val(j)]*(val(t-j)-val(j)) for j in S if t!=j)
                assert actual==2**(a-i)*retained_loss(a,i,q)
                checks+=1
            if a-u>=4:
                assert max(retained_loss(a,i,q) for i in range(u) if q[i]) >= Fraction(max(q),4*u)
    return checks

def check_minors():
    checks=0
    for a,i in [(3,0),(4,1),(5,2)]:
        m=2**(a-i-1)
        for k in range(1,m+1):
            def vandermonde(R):
                return sum(val(y-x) for x,y in combinations(R,2))
            vals=[vandermonde(R) for R in combinations(range(m),k)]
            # Cauchy's formula evaluated using integer valuations of all factors
            t=2**i; alpha=2**(a+1); T=t+alpha; stride=2**(i+1)
            grid=range(-2**a,2**a)
            norm=sum(val(T-z) for z in grid)-sum(val(z) for z in grid if z)
            floor=10**9
            for R in combinations(range(m),k):
                for C in combinations(range(m),k):
                    detval=k*norm+(i+1)*k*(k-1)+vandermonde(R)+vandermonde(C)
                    detval-=sum(val(T+stride*(x-y)) for x in R for y in C)
                    floor=min(floor,detval)
            expected=sum(a+1-i+2*b+2*val(factorial(b)) for b in range(k))
            assert min(vals)==sum(val(factorial(b)) for b in range(k))
            assert floor==expected
            checks+=1
    return checks

print("Checked",check_losses(),"retained-level identities and",check_minors(),"determinantal minima.")
