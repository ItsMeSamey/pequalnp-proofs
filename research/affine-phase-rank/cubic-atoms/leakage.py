from itertools import combinations
from collections import defaultdict
g = {sum((x>>i&1)<<(3*i) | (y>>i&1)<<(3*i+1) | ((x&y)>>i&1)<<(3*i+2) for i in range(3)) for x in range(8) for y in range(8)}
f={frozenset([x]) for x in g}
for _ in range(3):
    new=set()
    for s in f:
        u=min(s)
        for w in g:
            d=w^u
            if w in s: continue
            a={v^d for v in s}
            if a<=g:new.add(s|a)
    f=new
print(len(f),'clean three-flats')
leaks=defaultdict(set)
for s in f:
    v=min(s)
    for w in range(512):
        if w in s:continue
        ext=s|{w^v^u for u in s}
        out=frozenset(ext-g)
        if len(out)==4:leaks[out].add(ext)
print(sum(map(len,leaks.values())),'four-flats attaining 12 genuine points')
print('largest multiplicity for common 4-point leakage',max(map(len,leaks.values())))
pairs=[]
for bag in leaks.values():
    for a,b in combinations(bag,2):
        if not ((a&b)&g): pairs.append((a,b))
print(len(pairs),'pairs with disjoint genuine support and same leakage')
for a,b in pairs:
    rest=g-a-b
    options=[s for s in f if s<=rest]
    def cover(r):
        if not r:return []
        v=min(r)
        for s in options:
            if v in s and s<=r:
                sol=cover(r-s)
                if sol is not None:return [s]+sol
    sol=cover(rest)
    if sol is not None:
        print('admissible minimal-leakage support tiling', [sorted(s) for s in [a,b]+sol])
        break
else: print('no minimal-leakage 7-flat support tiling')
