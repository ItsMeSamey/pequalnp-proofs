"""Moment formula over rationals and Q[epsilon]/epsilon^2."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, prod
from random import Random
zero=(F(0),F(0))
one=(F(1),F(0))
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def mul(a,b): return (a[0]*b[0],a[0]*b[1]+a[1]*b[0])
def scale(a,k): return(a[0]*k,a[1]*k)
def series(a,b,n):
    ans=[zero]*(n+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b[:n-i+1]):
            ans[i+j]=add(ans[i+j],mul(x,y))
    return ans
def genbin(n,k): return F(prod(n-i for i in range(k)),factorial(k))
def box(a): return product(*(range(x+1) for x in a))
def diff(a,b): return (-1)**(sum(a)-sum(b))*prod(comb(i,j) for i,j in zip(a,b))

def check(seed):
    rng=Random(seed)
    c=1+seed%2
    C=[[rng.randrange(-3,4) for _ in range(4)] for _ in range(c)]
    pins={rng.randrange(4)} if seed%2 else set()
    groups=((0,1),(2,3))
    coeff=[[[tuple(F(rng.randrange(-4,5),rng.randrange(1,4)) for _ in range(2))
             for _ in range(c+1)] for _ in range(4)] for g in groups]
    def meas(g,bits): return tuple(sum(C[i][j]*b for j,b in zip(g,bits)) for i in range(c))
    def wt(gi,bits,y):
        row=coeff[gi][2*bits[0]+bits[1]]
        a=row[0]
        for i,v in enumerate(y): a=add(a,scale(row[i+1],v))
        return a
    direct=zero
    for x in product((0,1),repeat=4):
        if any(not x[j] for j in pins): continue
        y=meas(range(4),x)
        direct=add(direct,mul(wt(0,x[:2],y),wt(1,x[2:],y)))
    rec=zero
    for alpha in product(range(3),repeat=c):
        a=sum(alpha)
        if a>2: continue
        for beta in box(alpha):
            for gamma in box(alpha):
                whole=[one]+[zero]*a
                for gi,g in enumerate(groups):
                    subtotal=[zero]*(a+1)
                    for bits in product((0,1),repeat=len(g)):
                        if any(j in pins and not b for j,b in zip(g,bits)): continue
                        term=[wt(gi,bits,beta)]+[zero]*a
                        for i,expo in enumerate(meas(g,bits)):
                            unit=[scale(one,genbin(expo,k)*gamma[i]**k) for k in range(a+1)]
                            term=series(term,unit,a)
                        subtotal=[add(x,y) for x,y in zip(subtotal,term)]
                    whole=series(whole,subtotal,a)
                f=F(diff(alpha,beta)*diff(alpha,gamma),prod(factorial(i) for i in alpha))
                rec=add(rec,scale(whole[a],f))
    assert direct==rec,(seed,direct,rec)
if __name__=='__main__':
    for i in range(80): check(i)
    print('80 signed rational fiber sums and their Hasse coefficients match exhaustive summation.')
