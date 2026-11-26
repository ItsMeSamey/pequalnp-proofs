"""Enumerate affine families of binary 3 by 3 units with affine inversion."""
from collections import Counter

def inverse(a,n):
    mask=(1<<n)-1
    rows=[(a>>(n*i)&mask) | (1<<(n+i)) for i in range(n)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if rows[i]>>j&1),None)
        if pivot is None:
            return None
        rows[j],rows[pivot]=rows[pivot],rows[j]
        for i in range(n):
            if i!=j and rows[i]>>j&1:
                rows[i]^=rows[j]
    return sum((r>>n)<<(n*i) for i,r in enumerate(rows))

def census(n):
    identity=sum(1<<((n+1)*i) for i in range(n))
    f={}
    for x in range(1<<(n*n)):
        y=inverse(x^identity,n)
        if y is not None:
            f[x]=y^identity
    layer={frozenset({0})}
    counts=[]
    while layer:
        counts.append(len(layer))
        following=set()
        for space in layer:
            for v in f.keys()-space:
                if all((v^u) in f and f[v^u]==f[v]^f[u] for u in space):
                    following.add(space.union(v^u for u in space))
        layer=following
    return counts

if __name__=='__main__':
    for n in [1,2,3]:
        print(n,census(n))
