from pathlib import Path
from itertools import permutations,combinations
import sys
source=Path(sys.argv[1]);sys.path.insert(0,str(source))
from verify_packing import samples
rows,front,target=samples(source/'L-meta-18968.json')
P={(r&8191,(r>>13)&127) for i,r in enumerate(rows) if (target^front)>>i&1}
N={(r&8191,(r>>13)&127) for i,r in enumerate(rows) if not target>>i&1}
def img(m,g):return sum((1<<k) for j,k in enumerate(g) if m>>j&1)
def star(q):return sum({l for p,l in P if p>>q&1})
markers=[star(q) for q in range(13)];group=[]
for g in permutations(range(7)):
 vals=[img(z,g) for z in markers]
 if set(vals)!=set(markers):continue
 w=[markers.index(v) for v in vals]
 if {(img(q,w),img(l,g)) for q,l in N}!=N:continue
 group.append(g)
orbits={}
for x in combinations(range(7),3):
 key=min(tuple(sorted(g[j] for j in x)) for g in group)
 orbits.setdefault(key,[]).append(x)
print(len(group),len(orbits))
for x,v in orbits.items():print(''.join(map(str,x)),len(v))
