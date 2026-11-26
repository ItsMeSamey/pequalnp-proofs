from pathlib import Path
from pysat.solvers import Solver
from pysat.card import CardEnc
ctx={'__file__':str(Path(__file__).resolve().parents[1]/'seventeen-mixed'/'line_basis.py')}
exec(Path(ctx['__file__']).read_text().split('visits=0')[0],ctx)
rels=ctx['rels']
cnf=CardEnc.atmost(list(range(1,128)),9,top_id=127).clauses
for a,b in rels:cnf.append([i for i in range(1,128) if not a&~i and not b&i])
allfamilies=set()
for k in range(7):
 missing=1<<k
 with Solver(name='glucose4',bootstrap_with=cnf+[[-missing]]) as s:
  while s.solve():
   family=tuple(v for v in s.get_model() if 0<v<=127)
   assert len(family)==9 and sum(x.bit_count()==1 for x in family)==6
   assert all(x.bit_count()==1 or x.bit_count()==2 and x&missing for x in family)
   allfamilies.add(tuple(sorted(family)))
   s.add_clause([-v for v in family])
assert allfamilies=={tuple(map(int,l.split())) for l in Path(__file__).with_name('nine.txt').read_text().splitlines()[1:]}
print('9-line masks: complete SAT replay for 7 missing-singleton cases,',len(allfamilies),'families.')
