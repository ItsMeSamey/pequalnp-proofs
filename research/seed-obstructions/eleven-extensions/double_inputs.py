from pathlib import Path
from itertools import combinations
import sys
base=Path(sys.argv[1])
rels=[tuple(map(int,l.split())) for l in (base/'rel.txt').read_text().splitlines()]
t=[sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
for row in (base/'singleton.txt').read_text().splitlines():
 *f,b,_=map(int,row.split())
 if b!=15:continue
 print(*f)
 unique={m:[] for m in f}
 for p,n in rels:
  yes=[m for m in f if p&m and not n&m]
  if len(yes)==1:unique[yes[0]].append((p,n))
 for m in f:
  tests=set()
  if m.bit_count()>=2:
   for T in t:
    if m&~T:continue
    for a,b in combinations([i for i in range(13) if not T>>i&1],2):
     pair=1<<a|1<<b
     opts=[(p,n) for p,n in unique[m] if not pair&~n]
     tests.add(frozenset((p,n) for p,n in opts if not any(p==pp and n!=nn and not n&~nn for pp,nn in opts)))
  tests=sorted((s for s in tests if not any(q<s for q in tests)),key=lambda s:len(s))
  print(len(tests))
  for ss in tests:print(len(ss),*(k for pair in sorted(ss) for k in pair))
