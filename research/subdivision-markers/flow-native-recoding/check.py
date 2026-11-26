from itertools import combinations,permutations,product
from random import Random

colors=(0,1,2)
perms=list(permutations(colors))
allowed=[set(c) for n in (1,2) for c in combinations(colors,n)]
local=0
for lists in product(allowed,repeat=3):
    good=[p for p in perms if all(a in s for a,s in zip(p,lists))]
    assert len(good)<=2
    assert all(sum(a!=b for a,b in zip(x,y))>=2 for x,y in combinations(good,2))
    local+=1
rng=Random(729)
for m in range(3,120):
    default=[rng.randrange(3) for _ in range(m)]
    true=[rng.randrange(3) for _ in range(m)]
    counts=[sum(p[c]==v for c,v in zip(true,default)) for p in perms]
    assert sum(counts)==2*m and 3*max(counts)>=m
print(local,"local three-list cases; 117 six-permutation averages")
