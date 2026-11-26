from random import Random
from lift import build
from solver import parity
from test_lift import valid

rng = Random(7012)
repairs = 0
for k in range(240):
    n = rng.randrange(1,6)
    M = [rng.getrandbits(n) for _ in range(n)]
    base = rng.getrandbits(n)
    eq = [(m,parity(m&base)) for m in (rng.getrandbits(n) for _ in range(rng.randrange(3)))]
    expected = {x for x in range(1<<n) if valid(M,eq,x)}
    for kind in ('pairs','hub'):
        lift = build(M,eq,kind)
        found = {y&((1<<n)-1) for y in range(1<<len(lift.graph)) if valid(lift.graph,lift.equations,y)}
        assert expected == found
        for x in expected:
            assert valid(lift.graph,lift.equations,lift.repair(x))
            repairs += 1
print('240 full projection comparisons for each of both repair gadgets;',repairs,'repairs')
