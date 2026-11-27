from itertools import combinations, product
from functools import reduce
from operator import xor
from collections import Counter
from pathlib import Path
import runpy

config = runpy.run_path(str(Path(__file__).with_name('three-transfer-simplices.py')))
U, full, tests, invertible = (config[k] for k in ('universe','full','tests','invertible'))
cases = Counter()
for candidate in combinations(U,5):
    s = set(candidate)
    if not full(s):
        continue
    rem = U-s-set().union(*(q for q in tests if not q&s))
    if not rem:
        continue
    t, = rem
    coefficients, = [k for k in range(32)
        if all((k & (16|x)).bit_count()%2 == (x in invertible) for x in s)]
    assert (coefficients & (16|t)).bit_count()%2 == (t in invertible)
    nodes = {min(s)}
    for _ in s:
        nodes |= {x for x in s if any((x^y) not in invertible for y in nodes)}
    degrees = tuple(sorted(sum(y!=x and (x^y) not in invertible for y in s) for x in s))
    bary = next(k for k in (3,5) if any(reduce(xor,a)==t for a in combinations(s,k)))
    cases[len(nodes)==5,degrees,bary]+=1
assert sorted(cases.values()) == [96,144,576]
print(cases)
P=[{i for i in range(4) if m>>i&1} for m in range(1,16)]
real=set()
for a,b,c in product(P,repeat=3):
    s=frozenset({x+4*y for x in a for y in b}|{x+4*(x^z) for x in a for z in c}|{(y^z)+4*y for y in b for z in c})
    if len(s)==5 and full(s):
        assert not (U-s-set().union(*(q for q in tests if not q&s)))
        real.add(s)
assert len(real)==144
for s in real:
    sizes=Counter(len({x^y for x in s for y in q}) for q in real)
    assert sizes=={11:16,13:64,14:64}
print(sizes)
