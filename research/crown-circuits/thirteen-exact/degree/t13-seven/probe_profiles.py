from itertools import permutations
from collections import defaultdict
from pathlib import Path
import sys
base=Path(sys.argv[1]);cache={};data=defaultdict(set)
for raw in (base/'qmodels.in').read_text().splitlines():
 p,g,clean,branch,quart,dirty=map(int,raw.split())
 if p!=6 or branch.bit_count()!=4:continue
 priv=[i for i in range(p) if not branch>>i&1];bv=[i for i in range(p) if branch>>i&1]
 edges=[(1<<i)|(1<<j) for i in range(p) for j in range(i) if g>>(i*(i-1)//2+j)&1]
 internal=edges.copy()
 for i in range(p): edges +=[1<<i]*(3+(quart>>i&1)-sum((e>>i)&1 for e in internal))
 edges +=[0]*(13-len(edges))
 ud=dirty.bit_count()
 key=(tuple(edges),tuple(priv),tuple(bv),dirty)
 if key not in cache:
  best=None
  for pu in permutations(priv):
   if any(bool(dirty>>i&1)!=(j<ud) for j,i in enumerate(pu)):continue
   for pb in permutations(bv):
    tags=[]
    for e in edges:
     u=sum(((e>>v)&1)<<j for j,v in enumerate(pu))
     b=sum(((e>>v)&1)<<j for j,v in enumerate(pb))
     tags.append((4*u+b.bit_count(),(u<<4)|b))
    tags.sort();k=(tuple(z[0] for z in tags),tuple(z[1] for z in tags))
    if best is None or k<best:best=k
  cache[key]=best
 for common in ([0,1] if ud else [0]):data[ud,common].add(cache[key])
for (d,c),pairs in data.items():
 f=f'p6-2{d}{c}';idx={tuple(map(int,l.split())):j for j,l in enumerate((base/(f+'.in')).read_text().splitlines())}
 rows=sorted((idx[s],tags) for s,tags in pairs)
 (base/(f+'.graphs')).write_text(''.join(' '.join(map(str,(j,*v)))+'\n' for j,v in rows))
 print(f,len(rows))
