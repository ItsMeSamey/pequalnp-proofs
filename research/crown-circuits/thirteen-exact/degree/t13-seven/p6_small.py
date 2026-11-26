from pathlib import Path
from collections import defaultdict
from itertools import permutations
import sys
from p7_replay import signature
def patterns(lines):
 result=defaultdict(set)
 for line in lines:
  p,g,c,b,quart,dirty=map(int,line.split())
  if p!=6 or b.bit_count() not in (4,5):continue
  priv=[i for i in range(p) if not b>>i&1];s=len(priv)
  edges=[(1<<i)|(1<<j) for i in range(p) for j in range(i) if g>>(i*(i-1)//2+j)&1]
  ies=edges.copy()
  for i in range(p): edges+=[1<<i]*(3+(quart>>i&1)-sum((e>>i)&1 for e in ies))
  edges +=[0]*(13-len(edges));assert len(edges)==13
  d=dirty.bit_count()
  orders=[a for a in permutations(priv) if all((dirty>>a[j]&1)==(j<d) for j in range(s))]
  sig=min(signature(edges,b,a) for a in orders)
  result[s,d,0].add(sig)
  if s==2 and d:result[s,d,1].add(sig)
 return result
if __name__=='__main__':
 base=Path(sys.argv[1])
 for key,rows in patterns((base/'qmodels.in').read_text().splitlines()).items():
  (base/('p6-'+''.join(map(str,key))+'.in')).write_text(''.join(' '.join(map(str,r))+'\n' for r in sorted(rows)));print(key,len(rows))
