from random import Random
from itertools import product

def verify(rows,cls):
    groups=[[i for i,c in enumerate(cls) if c==j] for j in range(3)]
    for x in range(1<<len(rows)):
        g=[[i for i in group if x>>i&1] for group in groups]
        if not all(len(section)%2 for section in g):continue
        if any((x>>i&1) and (x&r).bit_count()%2 for i,r in enumerate(rows)):continue
        homogeneous=sum(((rows[i]>>j)&1)==((rows[j]>>k)&1)==((rows[k]>>i)&1) for i,j,k in product(*g))
        assert homogeneous%2

rng=Random(941)
for trial in range(1600):
    n=rng.randrange(3,11)
    colors=[0,1,2]+[rng.randrange(3) for _ in range(n-3)]
    loops=[rng.randrange(2) for c in range(3)]
    rows=[0]*n
    for i in range(n):
        for j in range(i):
            value=loops[colors[i]] if colors[i]==colors[j] else rng.randrange(2)
            if value:
                rows[i]|=1<<j
                rows[j]|=1<<i
    verify(rows,colors)
print('1,600 random graphs passed for every feasible support.')
