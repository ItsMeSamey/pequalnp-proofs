from pathlib import Path
from collections import Counter
from itertools import combinations,combinations_with_replacement
import sys
source=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent
sys.path.insert(0,str(source.resolve()))
from verify_mixed import coords,target
ss=[sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
ns=[coords(i) for i in range(676) if not target>>i&1]
alln=(1<<len(ns))-1
points=[sum(1<<j for j,(p,l) in enumerate(ns) if p>>i&1) for i in range(13)]
lines=[sum(1<<j for j,(p,l) in enumerate(ns) if l>>i&1) for i in range(7)]
def union(vs):
 r=0
 for v in vs:r|=v
 return r
pc=[union(points[i] for i in range(13) if k>>i&1) for k in range(8192)]
lc=[union(lines[i] for i in range(7) if k>>i&1) for k in range(128)]
def inside(s):return [i for i in range(13) if s>>i&1]
def failures(a,b):
 raw=lc[a]&lc[b]
 return tuple((t,u) for t,u in combinations(range(7),2) if not raw&pc[ss[t]]&pc[ss[u]])
if __name__=='__main__':
 cc=Counter()
 for a,b in combinations([s for s in range(1,128) if s.bit_count()>=2],2):
  h=failures(a,b);c=(a|b).bit_count()-2+bool(a&b)
  key=tuple(sorted(sum(t in e for e in h) for t in range(7) if any(t in e for e in h)))
  cc[c,key]+=1
 for c in range(2,7):print(c,{k:v for (n,k),v in cc.items() if n==c})
