from itertools import product
from math import prod
from random import Random
rng=Random(3492)
for trial in range(70):
    n=rng.randrange(1,6)
    arcs=[(j,i) for i in range(n) for j in range(n) if rng.randrange(3)==0]
    weight=[rng.randrange(-3,4) for i in range(n)]
    total=0
    ordinary=0
    antichain=0
    reach={(i,i) for i in range(n)}|set(arcs)
    for k in range(n):
        reach|={(i,j) for i in range(n) for j in range(n) if (i,k) in reach and (k,j) in reach}
    comps=sorted({tuple(j for j in range(n) if (i,j) in reach and (j,i) in reach) for i in range(n)})
    cyc=[C[0] for C in comps if len(C)>1 or (C[0],C[0]) in arcs]
    for mask in range(1<<len(cyc)):
        a=[v for i,v in enumerate(cyc) if mask>>i&1]
        if any(i!=j and (i,j) in reach for i in a for j in a):continue
        antichain+=(-1)**n*prod(-weight[j] for j in range(n) if any((i,j) in reach for i in a))
    for x in product((0,1),repeat=n):
        if all(x[i]==any(x[j] for j,v in arcs if v==i) for i in range(n)):
            ordinary+=(-1)**n*prod(-weight[i] for i in range(n) if x[i])
        for u in product((0,1),repeat=n):
            if any(s and t for s,t in zip(x,u)):continue
            for v in product((0,1),repeat=n):
                if any(s and t for s,t in zip(u,v)) or any(x[j] and v[i] for j,i in arcs):continue
                total+=(-1)**(sum(u)+sum(v))*prod(weight[i] for i in range(n) if x[i])
    assert ordinary==total==antichain
print('70 signed weighted graph/OR/antichain comparisons passed')
