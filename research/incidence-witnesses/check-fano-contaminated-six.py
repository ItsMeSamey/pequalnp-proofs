from pathlib import Path
from itertools import combinations
from collections import Counter
import runpy
d=runpy.run_path(str(Path(__file__).with_name('check-fano-eighteen-deletions.py')))
M=d['rows']; E=d['edges']; req=d['requirements']; allbits=(1<<21)-1
from contextlib import redirect_stdout
from io import StringIO
from functools import lru_cache
z={}; exec(Path(__file__).with_name('check-five-cold-lattice.py').read_text().split('for a,b in ((p,l),(l,p)):')[0],z)
@lru_cache(None)
def can(stars):
 if any(a&b==a for a,b in combinations(stars,2)) or any(a&b==b for a,b in combinations(stars,2)):return True
 with redirect_stdout(StringIO()):return z['check'](stars)
counts=Counter(); left=Counter()
for om in combinations(range(21),2):
 K=allbits^sum(1<<i for i in om)
 if all(w&K for w in req):continue
 for H in (63,4032):
  C=[c for c in range(12) if not H>>c&1]
  Ds=[c for c in C if any(not any(K>>i&1 and n>>h&1 and any(n&(e^(1<<c)) for e in E if e>>c&1) for i,n in enumerate(M)) for h in range(12) if H>>h&1 and (1<<h|1<<c) not in E)]
  assert len(Ds)<=1
  if not Ds:continue
  y=Ds[0]; C.remove(y)
  for sz in range(1,6):
   for S in combinations(C,sz):
    sm=sum(1<<v for v in S)
    U=0
    for e in E:
     if e&sm:U|=e&H
    # pin y before projection. every original retained n with n&U still forces
    # X zero on n without y, since p+c remains accepted and all other bits dominate.
    forced=[n for i,n in enumerate(M) if K>>i&1 and n&U]
    cert=[n for i,n in enumerate(M) if K>>i&1 and any(not ((n&(H|sm))&~z) for z in forced)]
    fails=[(h,c) for h in range(12) if H>>h&1 for c in C if (1<<h|1<<c) not in E and not any(n>>h&1 and n>>c&1 for n in cert)]
    cov=all(any(n>>h&1 for n in cert) for h in range(12) if H>>h&1)
    if len(fails)==1:
     h0,c0=fails[0]; hs=[h for h in range(12) if H>>h&1]
     stars=tuple(sum(1<<i for i,h in enumerate(hs) if (1<<c|1<<h) in E or (h,c)==(h0,c0)) for c in C)
     counts["missing-one-possible",can(stars)]+=1
    counts[sz, len(fails),cov]+=1
    if fails or not cov:left[sz,tuple(sorted(sum(bool(e>>c&1) for e in E) for c in S))]+=1
assert counts["missing-one-possible",False]==16 and not counts["missing-one-possible",True]
assert left=={(1,(3,)):64,(1,(2,)):16,(2,(2,3)):16}
print(counts,left,sep='\n')
