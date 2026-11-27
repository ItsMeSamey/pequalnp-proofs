import json
from pathlib import Path
E=[6,24,17,33,66,132,264,528,160,640,576,320,288]
Z=[m for m in range(1024) if all(m&e!=e for e in E) and all(any((m|1<<i)&e==e for e in E) for i in range(10) if not m>>i&1)]
A=(1<<13)-1;B=((1<<16)-1)<<13
def maximal(pool):
 ls=sorted(x for x in pool if x&A and x&B);occ=[bytearray((len(ls)+7)//8) for _ in range(29)]
 for k,x in enumerate(ls):
  for j in range(29):
   if x>>j&1:occ[j][k//8]|=1<<(k%8)
 rows=[int.from_bytes(a,'little') for a in occ];out=set()
 for x in ls:
  domains=[rows[j] for j in range(29) if x>>j&1];hit=domains[0]
  for r in domains[1:]:hit&=r
  if hit.bit_count()==1:out.add(x)
 return out
allforms=[set(),{sum(1<<j for j,e in enumerate(E) if e>>v&1)|sum(1<<(13+j) for j,z in enumerate(Z) if not z>>v&1) for v in range(10)}]
for n in range(2,6):
 pool=set(allforms[n-1])
 for k in range(1,n//2+1):
  for x in allforms[k]:
   for y in allforms[n-k]:
    pool.add(((x|y)&A)|((x&y)&B));pool.add(((x&y)&A)|((x|y)&B))
 allforms.append(pool);out=maximal(pool)
 expected={int(x) for x in json.loads(Path(f'../reductions/pareto-{n}.json').read_text())}
 assert out==expected
 print(n,len(pool),len(out),'exact equality',flush=True)
