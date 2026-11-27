"""Exhaustively check all surviving interface fibers and decoded original witnesses."""
from random import Random
from private_syndrome_elimination import reduce_flats, solve_cnf, values, row_basis

rng=Random(48071)
for _ in range(240):
    n=rng.randrange(1,7)
    flats=[[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,5))]
           for _ in range(rng.randrange(9))]
    if flats and rng.randrange(2):
        flats.append(flats[0])
    def valid(x):
        return all(any((a&x).bit_count()%2!=b for a,b in flat) for flat in flats)
    models=[x for x in range(1<<n) if valid(x)]
    r=reduce_flats(n,flats)
    if r.impossible:
        assert not models
        continue
    live=row_basis(n,(a for s in r.groups for a in s))
    allowed={values(live,x) for x in models}
    for x in range(1<<n):
        ok=all(values(s,x) not in denied for s,denied in r.groups.items())
        assert ok==(values(live,x) in allowed)
        if ok:
            lifted=r.lift(x)
            assert valid(lifted) and values(live,x)==values(live,lifted)

for _ in range(140):
    n=rng.randrange(1,7)
    clauses=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,5)))
             for _ in range(rng.randrange(9))]
    xor=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(4))]
    models=[v for v in range(1<<n) if all((a&v).bit_count()%2==b for a,b in xor)
            and all(any(bool(v>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)]
    x,_=solve_cnf(n,clauses,xor)
    assert x in models if models else x is None

# A saturated private fiber creates a shared prohibition that must merge.
flats=[[(1,0),(2,0)],[(1,0),(2,1)],[(1,1)]]
assert reduce_flats(2,flats).impossible
# Extremely wide group; lifting must not enumerate its large private cube.
x,r=solve_cnf(80,[tuple(range(1,81))])
assert x and not r.groups and len(r.steps[0].private)==80
# p=m on disjoint rank-two singletons, then empty residual, counts 3^m versus 4^m.
m=22
rows=[(2*i+1,2*i+2) for i in range(m)]
x,r=solve_cnf(2*m,rows,residual_seed=0)
assert x is not None and not r.groups and len(r.steps)==m
# Connected rank-three fan on one shared literal also has p=m before projection.
clauses=[(1,2*i+2,2*i+3) for i in range(m)]
x,r=solve_cnf(2*m+1,clauses)
assert x is not None and not r.groups and len(r.steps)==m
# An irreducible triangle falls through to the residual p backend.
x,r=solve_cnf(3,[(1,2),(2,3),(1,3)])
assert x is not None and len(r.groups)==3 and not r.steps
try:
    solve_cnf(3,[(1,2),(2,3),(1,3)],residual_seed=0)
except ValueError:
    pass
else:
    raise AssertionError("invalid external witness accepted")
print("240 exhaustive interface-fiber comparisons, 140 CNF/XOR comparisons, private-rank 80, merge and backend controls passed")
