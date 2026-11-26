"""Recover zero-score assignment mass from moments of signed violated clauses."""
from fractions import Fraction as F
from itertools import product
from math import prod
from random import Random

def solve(a,b):
    m=[[F(x) for x in row]+[F(y)] for row,y in zip(a,b)]
    for j in range(len(m)):
        p=next((i for i in range(j,len(m)) if m[i][j]),None)
        if p is None:
            return None
        m[j],m[p]=m[p],m[j]
        d=m[j][j]
        m[j]=[x/d for x in m[j]]
        for i in range(len(m)):
            if i!=j:
                d=m[i][j]
                m[i]=[x-d*y for x,y in zip(m[i],m[j])]
    return [row[-1] for row in m]

def recover(m,B):
    for r in range(1,B+1):
        h=[[m[i+j] for j in range(r)] for i in range(r)]
        c=solve(h,[-m[r+i] for i in range(r)])+[F(1)]
        if sum(c[j]*m[r+j] for j in range(r+1))==0:
            return 0 if c[0] else sum(c[j]*m[j-1] for j in range(1,r+1))/c[1]
    return None

def check(n,terms,B):
    scores=[sum(w for w,c in terms if all(x[abs(l)-1]!=(l>0) for l in c))
            for x in product(range(2),repeat=n)]
    m=[]
    for k in range(2*B+1):
        total=0
        for tup in product(terms,repeat=k):
            forced={l for _,c in tup for l in c}
            if not any(-l in forced for l in forced):
                total+=prod(w for w,_ in tup)*(1<<(n-len(forced)))
        m.append(total)
    assert m==[sum(z**k for z in scores) for k in range(2*B+1)]
    assert recover(m,B)==(scores.count(0) if len(set(scores))<=B else None)

rng=Random(1817)
tests=[(2,[],2),(2,[(-3,())],1),(2,[(2,(1,1)),(-2,(1,1)),(4,(2,-2))],2),
       (2,[(1,(1,)),(-2,(2,))],2)]
for _ in range(75):
    n=rng.randrange(1,5)
    terms=[(rng.randrange(-3,4),tuple(rng.choice((-1,1))*rng.randrange(1,n+1)
                                       for _ in range(rng.randrange(4)))) for _ in range(rng.randrange(1,5))]
    tests.append((n,terms,rng.randrange(1,4)))
for args in tests:
    check(*args)
print(len(tests),'cases passed, including false support promises')
