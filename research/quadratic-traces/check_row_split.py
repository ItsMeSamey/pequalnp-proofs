from itertools import combinations,product
from random import Random

def dot(x,y): return (x&y).bit_count()%2
def mv(A,v): return sum(dot(a,v)<<j for j,a in enumerate(A))
def linear(vs,i): return sumxor(v for j,v in enumerate(vs) if i>>j&1)
def sumxor(it):
    x=0
    for y in it: x ^= y
    return x

def extend(prefix,candidates):
    basis=[]; piv={}
    for v in [*prefix,*candidates]:
        u=v
        while u and u.bit_length() in piv: u ^= piv[u.bit_length()]
        if u:
            piv[u.bit_length()]=u
            basis.append(v)
    return basis

def null(rows,n):
    rows=rows[:]; piv=[]; r=0
    for p in range(n):
        i=next((i for i in range(r,len(rows)) if rows[i]>>p&1),None)
        if i is None: continue
        rows[r],rows[i]=rows[i],rows[r]
        for k in range(len(rows)):
            if k!=r and rows[k]>>p&1: rows[k]^=rows[r]
        piv.append(p); r+=1
    return [sum((rows[i]>>j&1)<<p for i,p in enumerate(piv))|(1<<j) for j in range(n) if j not in piv]

def pull(A,U):
    return [sum(dot(mv(A,u),v)<<j for j,v in enumerate(U)) for u in U]

def solve(A,B):
    n=len(A)
    if not n: return []
    radical=null(A,n)
    if radical:
        v=radical[0]; L=[v]; W=null([mv(B,v)],n)
    else:
        # Obtain T v by solving A w=B v via a column-elimination inverse.
        piv={}
        for j in range(n):
            k=1<<j; u=mv(A,k)
            while u.bit_length() in piv:
                z,y=piv[u.bit_length()];u^=z;k^=y
            piv[u.bit_length()]=(u,k)
        def T(v):
            z=mv(B,v); w=0
            while z:
                y,k=piv[z.bit_length()];z^=y;w^=k
            return w
        L=[]; v=1
        while len(extend(L,[v]))>len(L):
            L.append(v); v=T(v)
        W=null([mv(A,v) for v in L],n)
    U=extend(L,W)[len(L):]
    ans=solve(pull(A,U),pull(B,U))
    return L+[linear(U,v) for v in ans]

def spaces(n):
    for d in range(n+1):
        for piv in combinations(range(n),d):
            extra=[(i,c) for i,p in enumerate(piv) for c in range(p+1,n) if c not in piv]
            for k in range(1<<len(extra)):
                U=[1<<p for p in piv]
                for j,(i,c) in enumerate(extra):
                    if k>>j&1: U[i]|=1<<c
                yield U

def alt(n,mask):
    A=[0]*n
    for k,(i,j) in enumerate(combinations(range(n),2)):
        if mask>>k&1: A[i]|=1<<j; A[j]|=1<<i
    return A

n=4
forms=[alt(n,i) for i in range(64)]
ss=list(spaces(n))
iso=[[not any(pull(A,U)) for U in ss] for A in forms]
for i,A in enumerate(forms):
    for j,B in enumerate(forms):
        U=solve(A,B)
        assert len(U)==max(len(V) for k,V in enumerate(ss) if iso[i][k] and iso[j][k])
        assert not any(pull(A,U)) and not any(pull(B,U))
rng=Random(132)
for n in range(5,15):
    for _ in range(6):
        A,B=[alt(n,rng.getrandbits(n*(n-1)//2)) for _ in range(2)]
        U=solve(A,B)
        assert len(U)>=(n+1)//2 and not any(pull(A,U)) and not any(pull(B,U))
print("4096 pairs in dimension 4 matched the exhaustive optimum; 60 higher-dimensional witnesses passed")
