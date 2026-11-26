"""Direct check of the stationary eight-cell example in chart-pit.md."""
from collections import Counter, defaultdict
from functools import reduce
from itertools import combinations
from operator import xor

columns = (19,26,20,17,7,5,13,6,21,4)
ell, u = 205, 28
lift = [v | (((ell >> i) & 1) << 5) for i,v in enumerate(columns)]

def independent(cols):
    span = {0}
    for v in cols:
        if v in span:
            return 0
        span |= {x ^ v for x in span}
    return 1

cells = Counter()
for X in combinations(range(2,10),4):
    ordinary = [columns[i] for i in X]
    a = independent([columns[0],*ordinary])
    b = independent([columns[0]^columns[1],*ordinary])
    d = independent([lift[0],lift[1],*(lift[i] for i in X)])
    e = independent([u,*ordinary])
    cells[a*4+b*2+(d^e)] += 1
assert [cells[i] for i in range(8)] == [11,6,8,24,8,8,1,4]

at_cycle, at_cocycle = defaultdict(set), defaultdict(set)
for functional in range(32):
    cocycle = sum((((functional & v).bit_count() & 1) << i) for i,v in enumerate(columns))
    if not cocycle & 1:
        continue
    for cycle in range(1<<10):
        if not cycle & 2 or cocycle & cycle:
            continue
        if reduce(xor, (v for i,v in enumerate(columns) if (cycle >> i) & 1), 0):
            continue
        value = ((ell & cycle).bit_count()+(functional & u).bit_count()) & 1
        at_cycle[cycle].add(value)
        at_cocycle[cocycle].add(value)
assert len(at_cycle) == len(at_cocycle) == 3
assert all(len(s)==1 for s in [*at_cycle.values(), *at_cocycle.values()])
print('Verified eight chart cell counts and six stationary fibers.')
