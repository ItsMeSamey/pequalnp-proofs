from itertools import combinations,product
from random import Random
from cycle_syndrome import solve,build,apply_word

rng=Random(7319)
checks=0
for n in (1,3,5):
    edges=list(combinations(range(n),2))
    for trial in range(60):
        raw=build(n,[])
        raw.zero=sum(rng.choice([0,1,2,3,5,8,12,14,15])<<(4*i) for i in range(len(edges)))
        order=edges[:]
        rng.shuffle(order)
        expected=any(all(not (raw.zero>>(4*i+(c[u]^c[v])))&1 for i,(u,v) in enumerate(edges))
                     for c in product(range(4),repeat=n) if c[0]==0)
        for o in (None,order):
            w=solve(raw,o)
            assert (w is not None)==expected
            if w is not None:assert not apply_word(raw,w)&raw.zero
        checks+=1
assert solve(build(5,combinations(range(5),2))) is None
print(checks,'random pin sets, two orders, K5 UNSAT; all replayed')
