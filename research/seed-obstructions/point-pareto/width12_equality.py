"""Certify every five-gate, twelve-wire point boundary."""
from itertools import combinations
from pathlib import Path
import sys

from pysat.card import CardEnc
from pysat.solvers import Solver
from check import encode
from input import point_obligations

raw, rows = point_obligations(Path(sys.argv[1]))
banks = {tuple(map(int, row.split())) for row in Path(__file__).with_name('cost-five-width-twelve.txt').read_text().splitlines()}
assert len(banks) == 5 and all(len(b) == 12 for b in banks)
tuples = {tuple(x for x in bank if x not in raw) for bank in banks}
assert len(tuples) == 5 and all(len(t) == 5 for t in tuples)
clauses, masks, *_ = encode(raw, rows, 12, 5)
for t in sorted(tuples):
    clauses.append([-q if x>>j&1 else q for x,m in zip(t,masks) for j,q in enumerate(m)])
with Solver(name='cadical195', bootstrap_with=clauses) as solver:
    assert not solver.solve(), 'another five-gate tuple is possible'

complete = set()
initial = {z for a,b in combinations(raw,2) for z in (a|b,a&b)}
for t in sorted(tuples):
    assert set(t) <= initial
    signals = raw + list(t)
    flags = list(range(1,len(signals)+1))
    cover = CardEnc.atmost(flags,12).clauses
    for point, negative in rows:
        cover.append([q for q,x in zip(flags,signals) if x & point and not x & negative])
    with Solver(name='cadical195', bootstrap_with=cover) as solver:
        while solver.solve():
            model = set(solver.get_model())
            complete.add(tuple(sorted(x for x,q in zip(signals,flags) if q in model)))
            solver.add_clause([-q if q in model else q for q in flags])
assert complete == banks
print('All five computed-mask tuples are realizable and each has one twelve-wire boundary.')
