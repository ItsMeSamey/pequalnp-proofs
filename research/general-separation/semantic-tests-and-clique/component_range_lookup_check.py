"""Exact rooted-color lookup, deletion offsets and finite-difference modulus."""
from fractions import Fraction as F
from itertools import product
from math import comb,factorial

def weights(b,values):
    n=len(values)
    a=[[F(j**(b+i-1)) for j in range(1,n+1)]+[F(v)]
       for i,v in enumerate(values)]
    for j in range(n):
        p=next(i for i in range(j,n) if a[i][j])
        a[j],a[p]=a[p],a[j]
        d=a[j][j]
        a[j]=[z/d for z in a[j]]
        for i in range(n):
            if i!=j:
                c=a[i][j]
                a[i]=[x-c*y for x,y in zip(a[i],a[j])]
    return [row[-1] for row in a]

cases=0
for b in (1,2,9,40):
    for B in range(1,5):
        for f in product((0,1),repeat=B):
            coeff=weights(b,f)
            for k in sorted(set(range(1,8))|set(range(b,b+B))):
                value=sum(c*j**(k-1) for j,c in enumerate(coeff,1))
                if b<=k<b+B:
                    assert value==f[k-b]
                for removed in range(k+1):
                    residual=k-removed
                    # For an empty residual root one deleted component instead.
                    split=sum(c*j**(removed-(residual==0))*j**max(0,residual-1)
                              for j,c in enumerate(coeff,1))
                    assert split==value
                    cases+=1
for p in range(1,15):
    w=1
    while factorial(w)%(2**p):
        w+=1
    for k in range(1,65):
        z=sum((-1)**(j-1)*comb(w,j)*j**(k-1) for j in range(1,w+1))
        assert (z-int(k==1))%2**p==0
print(cases,'rational lookup/offset checks and 896 modular evaluations passed')
