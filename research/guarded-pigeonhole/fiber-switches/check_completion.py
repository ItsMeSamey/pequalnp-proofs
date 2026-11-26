from completion import *
from random import Random

def graph(n,edges):
    A=[0]*n
    for i,j in edges:A[i]|=1<<j;A[j]|=1<<i
    return A

def check(A,L,z):
    result=recognize(A,L,z)
    if result is None:return False
    B,R,b,T=result;n=len(A);mask=(1<<n)-1;ones=(1<<(2*n))-1
    assert bip(B) and len(basis(R))==len(L)
    out=set()
    for x in range(1<<n):
        if mv(L,x)!=z:continue
        y=mv(A,x);v=local((x|(y<<n))^ones,T)^ones
        u=v&mask;w=v>>n
        assert mv(B,u)==w and mv(R,u)==b and (x&y)==(u&w)
        out.add(u)
    assert out=={u for u in range(1<<n) if mv(R,u)==b}
    return True

rng=Random(110);found=0
for _ in range(120):
    n=rng.randrange(3,9);t=rng.randrange(0,4);L=[]
    while len(L)<t:
        x=rng.randrange(1,1<<n)
        if len(basis(L+[x]))>len(L):L.append(x)
    A=graph(n,[pair for pair in combinations(range(n),2) if rng.random()<.38])
    found+=check(A,L,rng.randrange(1<<t))
print('random examples:',120,'recognized, complete fibers checked:',found)
C5=[(i,(i+1)%5) for i in range(5)]
assert check(graph(5,C5),[7,9,18],7)
A=graph(11,C5+[(0,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,2)])
L=[(1<<5)|(1<<8),(1<<6)|(1<<9),(1<<7)|(1<<10)]
fiber=[x for x in range(1<<11) if mv(L,x)==7]
d=[x&mv(A,x) for x in fiber]
assert len(fiber)==256 and d.count(0)==16 and all(len({p>>i&1 for p in d})==2 and len({x>>i&1 for x in fiber})==2 for i in range(11))
assert not recognize(A,L,7)
print('biconnected obstruction: 256 fiber assignments, 16 witnesses, all 11 selectors and defects vary')
