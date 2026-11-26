"""Compare a linked packet transfer with exhaustive assignments to its edge bits."""
from fractions import Fraction
from itertools import product
from math import prod

def matmul(A,B):
    return [[sum(A[i][t]*B[t][j] for t in range(2)) for j in range(2)] for i in range(2)]

def transpose(A):
    return list(zip(*A))

def check(L,m):
    T=2*L+1
    grid=range(-L,L)
    N=Fraction(prod(T-q for q in grid),prod(-q for q in grid if q))
    w=N/T
    K=[[1,1-w],[0,w]]
    boundary=[[1,0],[0,1]]
    for i in range(m):
        boundary=matmul(boundary,transpose(K) if i%2==0 else K)
    exact=[[0,0],[0,0]]
    for bits in product(range(2),repeat=m+1):
        weight=1
        for i in range(m):
            x,y=bits[i:i+2] if i%2==0 else bits[i:i+2][::-1]
            weight*=K[y][x]
        exact[bits[0]][bits[-1]]+=weight
    assert exact==boundary
    assert boundary[0][0]*boundary[1][1]-boundary[0][1]*boundary[1][0]==w**m

for L in (2,4,8,16):
    for m in (2,4,6,8,10):
        check(L,m)
print("Verified 20 linked packet chains, all four boundary counts and determinants.")
