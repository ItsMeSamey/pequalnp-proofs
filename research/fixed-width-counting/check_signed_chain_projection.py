from itertools import product
from random import Random
from collections import Counter

rng=Random(147)
zeroes=0
for case in range(225):
    dims=[rng.randrange(1,5) for _ in range(rng.randrange(1,4))]
    visibles=rng.randrange(3)
    if sum(dims)+visibles>10: continue
    offsets=[sum(dims[:i]) for i in range(len(dims))]
    nv=sum(dims)
    gauge=[rng.randrange(2) for _ in range(nv)]
    rows=[]
    for _ in range(rng.randrange(2,11)):
        terms=[]
        for i,s in enumerate(dims):
            r=rng.randrange(s+1)
            if r:
                terms.append((i,r,rng.randrange(2)))
        vis=[(nv+i,rng.randrange(2)) for i in range(visibles) if rng.randrange(2)]
        rows.append((terms,vis))
    scores=Counter()
    for x in product(range(2),repeat=nv+visibles):
        true=True
        for terms,vis in rows:
            if any(x[i]!=b for i,b in vis): continue
            if any(any((x[j]^gauge[j])!=b for j in range(offsets[i]+dims[i]-r,offsets[i]+dims[i])) for i,r,b in terms): continue
            true=False
            break
        scores["direct"]+=true
    states=[[(b,l) for b in range(2) for l in range(1,s+1)] for s in dims]
    for state in product(*states):
        exponent=sum(max(s-l-1,0) for s,(_,l) in zip(dims,state))
        for visbits in product(range(2),repeat=visibles):
            if all(any(visbits[i-nv]!=b for i,b in vis) or
                   any(state[i][0]!=b or state[i][1]<r for i,r,b in terms) for terms,vis in rows):
                scores["projected"]+=2**exponent
    assert scores["direct"]==scores["projected"]
    zeroes+=1
print(f"{zeroes} exhaustive assignment/profile comparisons passed")
