from functools import cache
from itertools import combinations
from random import Random

def tri(a,b,c,t):
    z=0
    for i in range(t):
        d,e,f=[(v>>(3*i))&7 for v in (a,b,c)]
        z ^= int(d!=0 and e not in (0,d) and f not in (0,d,e,d^e))
    return z

def top(vec,t):
    @cache
    def rec(ids):
        if not ids: return 1
        a,*rest=ids
        s=0
        for b,c in combinations(rest,2):
            if tri(vec[a],vec[b],vec[c],t):
                s^=rec(tuple(i for i in rest if i not in (b,c)))
        return s
    return rec(tuple(range(len(vec))))

rng=Random(9014)
for t in (1,2,3):
    for _ in range(30):
        v=[1<<i for i in range(3*t)]
        for _ in range(5*len(v)):
            a,b=rng.sample(range(len(v)),2)
            v[a]^=v[b]
        assert top(v,t)==1
        v[1]=v[0]
        assert top(v,t)==0

# Enumerate subspaces via unique reduced echelon bases, checking T only on basis triples.
hist={}
for d in range(7):
    count=0
    for piv in combinations(range(6),d):
        slots=[(r,c) for r,p in enumerate(piv) for c in range(p+1,6) if c not in piv]
        for mask in range(1<<len(slots)):
            v=[1<<p for p in piv]
            for j,(r,c) in enumerate(slots):
                if mask >> j & 1: v[r]|=1<<c
            if all(tri(a,b,c,2)==0 for a,b,c in combinations(v,3)): count+=1
    hist[d]=count
assert max(k for k,v in hist.items() if v)==4
print("90 random bases and 90 singular tuples checked; all 6-bit subspaces enumerated:",hist)
