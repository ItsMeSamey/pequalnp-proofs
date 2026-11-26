"""Independent Gram basis of actual literal cubes, with local residual checks."""
from fractions import Fraction as F
from itertools import combinations
from random import Random

def meet(a,b):
    return (a[0]|b[0],a[1]|b[1])

def mass(n,a):
    return 0 if a[0]&a[1] else 1<<(n-(a[0]|a[1]).bit_count())

def solve(matrix,rhs):
    a=[[F(x) for x in row]+[F(v)] for row,v in zip(matrix,rhs)]
    for i in range(len(a)):
        p=next((j for j in range(i,len(a)) if a[j][i]),None)
        if p is None:
            return None
        a[i],a[p]=a[p],a[i]
        z=a[i][i]
        a[i]=[x/z for x in a[i]]
        for j in range(len(a)):
            if i!=j:
                z=a[j][i]
                a[j]=[x-z*y for x,y in zip(a[j],a[i])]
    return [row[-1] for row in a]

def check(n,cs):
    if not cs:
        return
    def value(c,x):
        return int(c[0]&~x==0 and c[1]&x==0)
    def gram(cols):
        return [[mass(n,meet(c,d)) for d in cols] for c in cols]
    truth=[int(any(value(c,x) for c in cs)) for x in range(1<<n)]
    basis=[]
    candidates=cs
    for k in range(1,len(cs)+1):
        for c in dict.fromkeys(candidates):
            b=basis+[c]
            if mass(n,c)>0 and solve(gram(b),[0]*len(b)) is not None:
                basis=b
        rhs=[mass(n,c) for c in basis]
        alpha=solve(gram(basis),rhs)
        complete=True
        for d in cs:
            err=mass(n,d)-2*sum(a*mass(n,meet(c,d)) for a,c in zip(alpha,basis))
            err+=sum(a*b*mass(n,meet(meet(c,e),d)) for a,c in zip(alpha,basis) for b,e in zip(alpha,basis))
            complete &= err==0
        # Independently enumerate every product and check its truth-vector span.
        piv={}
        def reduce(r):
            r=list(map(F,r))
            for p,v in sorted(piv.items()):
                z=r[p]
                r=[x-z*y for x,y in zip(r,v)]
            return r
        for j in range(1,k+1):
            for inds in combinations(cs,j):
                r=reduce([int(all(value(c,x) for c in inds)) for x in range(1<<n)])
                if any(r):
                    p=next(i for i,x in enumerate(r) if x)
                    piv[p]=[v/r[p] for v in r]
        assert len(piv)==len(basis) and complete==(not any(reduce(truth)))
        if complete:
            assert sum(a*z for a,z in zip(alpha,rhs))==sum(truth)
            return k
        candidates=[meet(c,d) for c in basis for d in cs]
    raise AssertionError('failed to represent union')

assert check(6,[(3,0),(12,0),(48,0)])==3
assert check(3,[(1,0),(2,1),(4,3),(0,7)])==1
rng=Random(192)
for _ in range(40):
    cs=[(rng.randrange(8),rng.randrange(8)) for _ in range(4)]
    check(3,cs)
print('42 systems; exact dimension, local residual, first degree and count passed')
