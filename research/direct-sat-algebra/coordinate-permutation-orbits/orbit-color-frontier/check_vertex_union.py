from itertools import combinations,product
from random import Random
from vertex_union import solve,apply_word,build

rng=Random(8502)
checks=0
for n in (1,3,5,7):
    edges=list(combinations(range(n),2))
    for trial in range(30 if n<7 else 4):
        raw=build(n,[])
        raw.zero=sum(rng.choice((0,0,1,2,3,4,8,10,14,15))<<(4*i) for i in range(len(edges)))
        ok=any(all(not raw.zero>>(4*i+(c[x]^c[y]))&1 for i,(x,y) in enumerate(edges))
               for c in product(range(4),repeat=n) if c[0]==0)
        order=list(range(n))
        rng.shuffle(order)
        for o in (None,order):
            w=solve(raw,o)
            assert (w is not None)==ok
            if w is not None:assert not apply_word(raw,w)&raw.zero
        checks+=1
for ground,r,ok in ((5,1,False),(5,2,True),(6,2,True),(7,2,False)):
    vertices=list(map(set,combinations(range(ground),r)))
    raw=build(len(vertices),[(i,j) for i,j in combinations(range(len(vertices)),2)
                             if vertices[i].isdisjoint(vertices[j])])
    w=solve(raw)
    assert (w is not None)==ok
    if w is not None:assert not apply_word(raw,w)&raw.zero
print(checks,'random pin fixtures, two orders, and four Kneser decisions passed')
