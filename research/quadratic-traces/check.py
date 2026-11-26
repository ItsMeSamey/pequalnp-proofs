"""Finite verification of the optimum pencil rank and graphical trace formulas."""
from itertools import combinations,product
import random

def gf_mul(a,b):
    v=0
    while b:
        if b&1:
            v^=a
        b>>=1; a<<=1
        if a&16:
            a^=19
    return v

def rank(M):
    M=[r[:] for r in M]; i=0
    for j in range(len(M[0])):
        p=next((k for k in range(i,len(M)) if M[k][j]),None)
        if p is None:
            continue
        M[i],M[p]=M[p],M[i]
        for k in range(i+1,len(M)):
            c=M[k][j]
            if c:
                a=M[i][j]
                M[k]=[gf_mul(a,x)^gf_mul(c,y) for x,y in zip(M[k],M[i])]
        i+=1
    return i

def subspaces(n):
    spaces={frozenset([0]):[]}
    for x in range(1,1<<n):
        for S,B in list(spaces.items()):
            if x not in S:
                spaces.setdefault(S|{y^x for y in S},B+[x])
    return list(spaces.values())

def evaluate(M,x,y):
    return sum(M[i][j] for i in range(len(M)) if x>>i&1
                        for j in range(len(M)) if y>>j&1)%2

def mask_form(B):
    return sum(1<<j for j,(u,v) in enumerate(combinations(range(len(B)),2)) if B[u][v])

def orthogonal_mask(n,basis):
    edges=list(combinations(range(n),2))
    return [sum(1<<p for p,(a,b) in enumerate(edges)
                if ((x>>a&1)*(y>>b&1))^((x>>b&1)*(y>>a&1)))
            for x,y in combinations(basis,2)]

rng=random.Random(83); cases=0
for n in range(2,7):
    spaces=subspaces(n)
    tests=[(len(B),orthogonal_mask(n,B)) for B in spaces]
    for _ in range(16):
        A=[[0]*n for i in range(n)]
        B=[[0]*n for i in range(n)]
        for i,j in combinations(range(n),2):
            A[i][j]=A[j][i]=rng.randrange(2)
            B[i][j]=B[j][i]=rng.randrange(2)
        a,b=mask_form(A),mask_form(B)
        optimum=max(d for d,V in tests if all(not ((q&a).bit_count()%2 or (q&b).bit_count()%2) for q in V))
        # A nonzero minor has degree at most n<16, so some GF(16) value attains its rank.
        R=max(rank([[A[i][j]^gf_mul(t,B[i][j]) for j in range(n)] for i in range(n)]) for t in range(16))
        assert optimum==n-R//2
        cases+=1
print("Compared common isotropic optima with normal pencil ranks for",cases,"pairs.")
n=4
edges=list(combinations(range(n),2))
tests=[(len(B),orthogonal_mask(n,B)) for B in subspaces(n)]
for graph in range(1<<len(edges)):
    opt=max(d for d,V in tests if all(not (q&graph) for q in V))
    independent=max(S.bit_count() for S in range(1<<n) if all(
        not ((graph>>k&1) and (S>>a&1) and (S>>b&1)) for k,(a,b) in enumerate(edges)))
    assert opt==independent
print("Verified graphical isotropic optima on all 64 labelled four-vertex graphs.")
