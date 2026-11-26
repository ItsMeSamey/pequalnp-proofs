from itertools import permutations
from collections import Counter
from pathlib import Path
seen=set()
for l in Path('models.tsv').read_text().splitlines():
 p,g,c,b,q,d=map(int,l.split())
 if b.bit_count()!=3:continue
 B=[i for i in range(6) if b>>i&1]; U=[i for i in range(6) if not b>>i&1]
 E=[(i,j) for i in range(6) for j in range(i) if g>>(i*(i-1)//2+j)&1]
 if len(E)<2:continue
 if sum((i in B)!=(j in B) for i,j in E)>3+d.bit_count():continue
 best=None
 for bs in permutations(B):
  for us in permutations(U):
   perm=bs+us
   qt=sum(((q>>v)&1)<<j for j,v in enumerate(perm));dt=sum(((d>>v)&1)<<j for j,v in enumerate(perm))
   edges=tuple(sorted((1<<perm.index(i))|(1<<perm.index(j)) for i,j in E))
   key=(edges,qt,dt)
   if best is None or key<best:best=key
 seen.add(best)
rows=sorted(seen)
Path('types.tsv').write_text(''.join(' '.join(map(str,[i,q,d,*E]))+'\n' for i,(E,q,d) in enumerate(rows)))
print(len(rows),Counter(len(E) for E,q,d in rows),len({E for E,q,d in rows}))
