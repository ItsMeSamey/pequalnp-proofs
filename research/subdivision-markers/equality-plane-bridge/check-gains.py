"""Audit arbitrary two-bit edge shifts on the odd-rim join."""
from random import Random
from itertools import product
from check import graph

def corrected(L,g):
    E=graph(L)
    gauge=(0,)+tuple(g[:L+1])
    z=[v^gauge[u]^gauge[w] for v,(u,w) in zip(g,E)]
    spoke=z[L+1:2*L+1]
    ring=z[2*L+1:]
    if any(spoke):
        last=next(i for i,v in enumerate(spoke) if v)
        hub=spoke[last]
        ordering=[(last+1+j)%L for j in range(L)]
    elif any(ring):
        cut=next(i for i,v in enumerate(ring) if v)
        hub=next(v for v in (1,2,3) if v!=ring[cut])
        ordering=[(cut+1+j)%L for j in range(L)]
    else:
        return None
    x=[0,hub]+[None]*L
    for i in ordering:
        banned={0,hub^spoke[i]}
        prev=(i-1)%L; nxt=(i+1)%L
        if x[2+prev] is not None:
            banned.add(x[2+prev]^ring[prev])
        if x[2+nxt] is not None:
            banned.add(x[2+nxt]^ring[i])
        x[2+i]=next(v for v in range(4) if v not in banned)
    return tuple(v^a for v,a in zip(x,gauge))

rng=Random(12554)
count=0
for L in (3,5,7,9):
    shifts=product(range(4),repeat=2*L) if L==3 else (
        [rng.randrange(4) for _ in range(2*L)] for _ in range(1000))
    for residue in shifts:
        E=graph(L)
        gauge=[rng.randrange(4) for j in range(L+2)]
        z=[0]*(L+1)+list(residue)
        gain=[v^gauge[i]^gauge[j] for v,(i,j) in zip(z,E)]
        x=corrected(L,gain)
        assert (x is not None)==any(residue)
        if x is not None:
            assert all(x[i]^x[j]^g for g,(i,j) in zip(gain,E))
        count+=1
print('two-bit gain scenarios',count)
