from random import Random
from functools import reduce
def mul(a,b):
    s=0
    while b:
        if b&1:s^=a
        b>>=1;a<<=1
        if a&16:a^=19
    return s
def prod(l):return reduce(mul,l,1)
def inv(a):return next(i for i in range(1,16) if mul(i,a)==1)
def det(m):
    a=[row[:] for row in m];d=1
    for j in range(len(a)):
        k=next((i for i in range(j,len(a)) if a[i][j]),None)
        if k is None:return 0
        a[k],a[j]=a[j],a[k]
        v=a[j][j];d=mul(d,v);row=[mul(b,inv(v)) for b in a[j]]
        for i in range(j+1,len(a)):
            w=a[i][j];a[i]=[u^mul(w,b) for u,b in zip(a[i],row)]
    return d
def diag(a,w):
    return [[v^(w[i] if i==j else 0) for j,v in enumerate(row)] for i,row in enumerate(a)]
rng=Random(7621)
for _ in range(200):
    n=rng.randrange(1,7)
    def mat():
        a=[[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(i+1):a[i][j]=a[j][i]=rng.randrange(2)
        return a
    a,b=mat(),mat()
    y=[rng.choice([0,*range(2,16)]) for _ in range(n)]
    w=[mul(v,v) for v in y]
    h=[mul(z,inv(z^1)) for z in w];t=[mul(v,inv(z^1)) for v,z in zip(y,w)]
    cross=diag([[0]*n for i in range(n)],t)
    c=[u+v for u,v in zip(diag(a,h),cross)]+[u+v for u,v in zip(cross,diag(b,h))]
    rhs=mul(prod([z^1 for z in w]),det(c));lhs=0
    for x in range(1<<n):
        bits=[x>>i&1 for i in range(n)]
        if det(diag(a,bits)) and det(diag(b,bits)):
            lhs ^= prod(v for bit,v in zip(bits,w) if bit)
    assert lhs==rhs
print('200 GF(16) weighted identities passed')
