"""Triangular dictionary localized to one rectangle of independent ISA inputs."""
from itertools import product

def response(i,j):
    return int(i==j or (j<i and (i-j)%2==1))

def coefficients(t):
    out=[]
    for i in range(1,t+1):
        out.append(1-sum(c*response(i,j) for j,c in enumerate(out,1)))
    return out

# Two banks, two rows apiece, binary pointers and two payload bits in each.
# On primary rectangle (0,0) the two unused pointers supply a four-cell tag.
c=coefficients(4)
cases=0
for b in product(range(2),repeat=10):
    i,h,p0,p1,q0,q1,y0,y1,z0,z1=b
    f=(y0,y1)[(p0,p1)[i]]*(z0,z1)[(q0,q1)[h]]
    special=(i,h)==(0,0)
    tag=1+p1+2*q1
    val=sum(c[j-1]*f*special*response(tag,j) for j in range(1,5))
    val+=sum(f*int((i,h)==pair) for pair in ((0,1),(1,0),(1,1)))
    assert val==f
    cases+=1
t=30
c=coefficients(t)
fib=[0,1]
for i in range(t):
    fib.append(sum(fib[-2:]))
assert all(abs(c[i-1])==fib[i-2] for i in range(2,t+1))
# Dual localized on one yes input per tag: A.T z=e_t, hence <z,1>=c_t.
z=[0]*t
for j in reversed(range(t)):
    z[j]=int(j==t-1)-sum(z[i]*response(i+1,j+1) for i in range(j+1,t))
assert sum(z)==c[-1] and all(sum(z[i]*response(i+1,j+1) for i in range(t))==int(j==t-1) for j in range(t))
print(cases,'full inputs; t=30 forced last coefficient',c[-1], 'and dual checked')

from fractions import Fraction

assert sum(map(abs,z))==fib[t+1]
assert Fraction(abs(c[-1]),sum(map(abs,z)))==Fraction(317811,1346269)
assert abs(c[-1])-Fraction(1,5)*sum(map(abs,z))==Fraction(242786,5)
# Adding the missing indicator gives an exact unit-coefficient full-cube sum.
for b in product(range(2),repeat=10):
    i,h,p0,p1,q0,q1,y0,y1,z0,z1=b
    f=(y0,y1)[(p0,p1)[i]]*(z0,z1)[(q0,q1)[h]]
    assert sum(int((i,h)==(a,b0))*(y0,y1)[(p0,p1)[a]]*
               (z0,z1)[(q0,q1)[b0]] for a,b0 in product(range(2),repeat=2))==f
print('Exact fractions, missing-feature restoration and target values passed')
