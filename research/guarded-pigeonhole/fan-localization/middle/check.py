from itertools import combinations
from random import Random

def make(n, edge_mask, k):
    L,a,b,R=n,n+1,n+2,n+3
    A=[0]*(n+4)
    def add(u,v):
        A[u]|=1<<v
        A[v]|=1<<u
    for u,v in ((L,a),(a,b),(b,R)):
        add(u,v)
    choices=[(u,v) for u in range(k) for v in range(k,n)]
    choices.extend((u,R if u<k else L) for u in range(n))
    for i,(u,v) in enumerate(choices):
        if edge_mask>>i&1:
            add(u,v)
    return A


def connected(A):
    s=1
    while True:
        old=s
        for i,row in enumerate(A):
            if s>>i&1:
                s|=row
        if s==old:
            return s==(1<<len(A))-1


def rank(rows):
    basis={}
    for x in rows:
        while x and x.bit_length() in basis:
            x^=basis[x.bit_length()]
        if x:
            basis[x.bit_length()]=x
    return len(basis)


def models(A):
    return [s for s in range(1<<len(A)) if
            not any(s>>i&1 and (s&r).bit_count()%2 for i,r in enumerate(A))]


if __name__=='__main__':
    total=cuts=bridges=extensions=0
    for n,k in [(2,1),(3,1),(4,2)]:
        for raw in range(1<<(n+k*(n-k))):
            A=make(n,raw,k)
            if not connected(A):
                continue
            total+=1
            L,a,b,R=range(n,n+4)
            full=(1<<len(A))-1
            has_central=False
            for x in range(full):
                if not x>>L&1 or min(x.bit_count(),(full^x).bit_count())<2:
                    continue
                if rank((r&~x for i,r in enumerate(A) if x>>i&1))!=1:
                    continue
                cuts+=1
                modes=tuple((x>>i)&1 for i in [L,a,b,R])
                assert modes in ((1,1,1,1),(1,0,0,0),(1,1,0,0),(1,1,1,0))
                cross=[(i,j) for i,r in enumerate(A) if x>>i&1
                       for j in range(len(A)) if not x>>j&1 and r>>j&1]
                if modes==(1,1,0,0):
                    assert cross==[(a,b)]
                    has_central=True
                if modes==(1,0,0,0):
                    assert all(i==L for i,j in cross)
                if modes==(1,1,1,0):
                    assert all(j==R for i,j in cross)
            m=models(A)
            if has_central:
                bridges+=1
                tied={s for s in m if (s>>L^s>>R)&1==0}
                priv=(1<<a)|(1<<b)
                assert {s&~priv for s in tied}=={s for s in tied if not s&priv}
            E=A+[1<<L,1<<R]
            E[L]|=1<<len(A)
            E[R]|=2<<len(A)
            assert set(m)=={s&full for s in models(E)}
            extensions+=1
    print('connected graphs, proper cuts, central bridge graphs, universal extensions:',total,cuts,bridges,extensions)
