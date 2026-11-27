from itertools import product
from collections import Counter
from original_dense_driver import count,witness,leaves
cases=[(2,[(1,2),(1,-2),(-1,2),(-1,-2)]),(2,[(1,2),(1,-2),(-1,2)]),
       (3,[(1,2,3),(1,2,-3),(-1,-2,3),(-1,-2,-3)]),
       (2,[(-2,),(-2,1),(2,-1)]),(0,[()])]
for n,f in cases:
    xs=[x for x in product((0,1),repeat=n) if all(any(x[abs(v)-1]==int(v>0) for v in c) for c in f)]
    stats=Counter()
    assert count(n,f,stats)==len(xs) and witness(n,f)==(min(xs) if xs else None)
    print(n,len(f),len(xs),dict(stats))
# Force a nonroot disjoint split at a small auxiliary threshold and validate all fibers.
f=[(1,2),(1,3),(1,4)]
parts=list(leaves(f,2))
for x in product((0,1),repeat=4):
    sat=lambda g:all(any(x[abs(z)-1]==int(z>0) for z in c) for c in g)
    assert sum(sat(g) for g in parts)==int(sat(f))
