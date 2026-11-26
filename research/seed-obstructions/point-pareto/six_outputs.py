"""Enumerate the arbitrary singleton-signature banks before charging point gates."""
from itertools import combinations
from pathlib import Path
import sys
from collections import Counter
from pysat.solvers import Solver
from input import point_obligations
from check import encode

raw, rows = point_obligations(Path(sys.argv[1]))
# An arbitrary selected bank with at most five nonraw signatures can use unused
# distinct formal slots, so we constrain the total *selected* count only.
clauses, *_ = encode(raw, rows, 11, 5, abstract=True)
with Solver(name='cadical195', bootstrap_with=clauses) as solver:
    assert not solver.solve()
stars = [sum(1 << ((j+6+d) % 13) for d in (0,1,3,9)) for j in range(7)]
assert all((a & t).bit_count() <= 1 for a in raw for t in stars)
shallow = {z for a,b in combinations(raw, 2) for z in (a|b,a&b)}
all_masks = set()
counts = Counter()
clauses, masks, *_ = encode(raw, rows, 11, 6, selected=6, abstract=True)
with Solver(name='cadical195', bootstrap_with=clauses) as solver:
    while solver.solve():
        model = set(solver.get_model())
        bank = [sum((q in model) << bit for bit,q in enumerate(m)) for m in masks]
        hosts = [[j for j,t in enumerate(stars) if not x & ~t] for x in bank]
        assert all(len(h) == 1 for h in hosts)
        assert len({h[0] for h in hosts}) == 6
        assert len(set(bank) & shallow) <= 3
        assert all(x.bit_count() >= 3 for x in set(bank) - shallow)
        counts[len(set(bank) & shallow)] += 1
        all_masks.update(bank)
        solver.add_clause([(-q if x >> i & 1 else q) for x,m in zip(bank,masks) for i,q in enumerate(m)])
assert counts == Counter({0:6064,1:7392,2:1968,3:192})
assert all_masks == {x for x in range(8192) if x.bit_count() >= 2 and any(not x & ~t for t in stars)}
print('No width-eleven bank uses five or fewer nonraw masks.')
print('Six-mask banks:',sum(counts.values()),'distinct masks:',len(all_masks),'shallow histogram:',sorted(counts.items()))
