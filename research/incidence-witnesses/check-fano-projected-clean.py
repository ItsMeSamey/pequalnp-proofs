from pathlib import Path
from itertools import combinations
from collections import Counter,defaultdict
import runpy
d=runpy.run_path(str(Path(__file__).with_name('check-fano-eighteen-deletions.py')))
M=d['rows']; E=d['edges']; req=d['requirements']; allbits=(1<<21)-1

out=Counter(); decisions=Counter()
for k in (1,2):
 for omitted in combinations(range(21),k):
  K=allbits^sum(1<<i for i in omitted)
  if not all(w&K for w in req):continue
  for H in (63,4032):
   cold=[c for c in range(12) if not H>>c&1]
   for size in range(1,7):
    for S in combinations(cold,size):
     sm=sum(1<<v for v in S)
     deg=tuple(sorted(sum(bool(e>>v&1) for e in E) for v in S))
     U=0
     for e in E:
      if e&sm:U|=e&H
     forced=[n for i,n in enumerate(M) if K>>i&1 and n&U]
     certified=[n for i,n in enumerate(M) if K>>i&1 and any(not ((n&(H|sm))&~z) for z in forced)]
     cm=sum(1<<i for i,n in enumerate(M) if n in certified)
     if len(certified)>=19 or (len(certified)>=17 and all(w&cm for w in req)):key="old projection"
     elif size==1 or deg==(2,3):key="direct pin"
     else:
      assert all(any(n>>v&1 for n in certified) for v in range(12))
      bad={c for c in cold for h in range(12) if H>>h&1 and (1<<h|1<<c) not in E and not any(n>>c&1 and n>>h&1 for n in certified)}
      assert len(bad)<=1, (omitted,H,S,bad)
      key="projected clean shore" if not bad else "projected clean pin"
     decisions[k,key]+=1
  out[k]+=1
assert out=={1:21,2:198}
print(dict(out),dict(decisions))
