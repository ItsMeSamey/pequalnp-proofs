from collections import Counter
from itertools import combinations_with_replacement
from pathlib import Path
from zipfile import ZipFile
from pysat.card import CardEnc
from pysat.solvers import Solver
import os,sys
os.chdir(sys.argv[1]);sys.path.insert(0,str(Path.cwd()))
from inputs import P,N
from price_filter import price
raw=tuple(1<<i for i in range(7))
clauses={tuple(m for m in range(1,128) if m&(p>>13) and not m&(n>>13)) for p in P for n in N if not (p&8191)&~(n&8191)}
expected={tuple(map(int,x.split())) for x in ZipFile('twelve-eight.zip').read('twelve-eight/exceptional-nine.txt').decode().splitlines()}
found=set()
with Solver(name='cadical195',bootstrap_with=list(clauses)+[[-x for x in raw]]+CardEnc.atmost(list(range(1,128)),9).clauses)as s:
 while s.solve():
  m=tuple(sorted(x for x in s.get_model() if 1<=x<=127))
  assert len(m)==9
  found.add(m);s.add_clause([-x for x in m])
assert found==expected
print('distinct line obligation clauses',len(clauses),'missing-literal covers',len(found))
def independent(t):
 boxes=set(t);big=[x for x in boxes if x.bit_count()>1];dup=len(t)-len(boxes-{0})
 if len(big)==3:return 3+dup
 if len(big)<2:return dup+sum(m.bit_count()-1 for m in big)
 a,b=big;return dup+(a|b).bit_count()-(1 if a&b else 2)
full={tuple(sorted((*raw,a,b))) for a,b in combinations_with_replacement(range(128),2)}|found
assert len(full)==8280 and all(price(t)==independent(t)for t in full)
print('physical line price histogram',sorted(Counter(independent(t)for t in full).items()))
