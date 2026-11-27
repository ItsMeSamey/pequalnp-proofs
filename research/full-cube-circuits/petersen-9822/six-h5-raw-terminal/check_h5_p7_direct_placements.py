"""Direct original-mask census. Output: leak index, four widths, oriented placements, productive/leaky placements."""
from itertools import combinations_with_replacement
import sys
from collections import Counter
from h5_three_sink_leak_sets import N,EDGES,CASES
R=1023; profiles=[w for w in combinations_with_replacement(range(1,10),4) if sum(w)==11 and w.count(1)<=2]; by={k:[i for i in range(1,1024) if i.bit_count()==k] for k in range(1,11)}
def ok(a,b):return a!=b and (a&b).bit_count()<=1
for ix in (list(map(int,sys.argv[1:])) or [2,8,11,18,29,44,65,114]):
 i,j=CASES[ix];m=R^N[i];n=R^N[j]; candidates=set()
 for y in [s for s in range(1,1024) if s&(m&n)==s]:
  for a in range(1,1024):
   if a|y!=m:continue
   for b in range(1,1024):
    if b|y!=n or not ok(a,b):continue
    remainder=11-a.bit_count()-b.bit_count()
    for k in range(1,1+remainder//2):
     rest=(k,remainder-k)
     if not any(y&t==y for t in (a,b)) and max(rest)<y.bit_count():continue
     for c in by[rest[0]]:
      if not all(ok(c,v) for v in (a,b)):continue
      eligible=by[rest[1]]
      if not any(y&t==y for t in (a,b,c)):
       eligible=[d for d in eligible if d&y==y]
      for d in eligible:
       if rest[0]==rest[1] and d<c:continue
       if not all(ok(d,v) for v in (a,b,c)):continue
       if not any(y&t==y for t in (a,b,c,d)):continue
       ab=tuple(sorted((a,b)));cd=tuple(sorted((c,d)))
       for sc,h in [((*ab,*cd),1024),((*cd,*ab),2048)]:
        candidates.add((*sc,h|y))
 count=Counter(); good=Counter(); useful=Counter()
 for a,b,c,d,u in candidates:
  if not u&1024:continue
  key=tuple(sorted(s.bit_count() for s in (a,b,c,d)))
  count[key]+=1
  if all(any(x&l and x&r for x in rows) for l,r in ((a,b),(c,d)) for rows in (EDGES,N)):
   good[key]+=1
   if all((l&r) not in (l,r) for l,r in ((a,b),(c,d))):useful[key]+=1
 from pathlib import Path
 Path('/tmp/h5-p7-physical-'+str(ix)+'.txt').write_text(''.join(' '.join(map(str,t))+'\n' for t in sorted(candidates) if t[-1]&1024))
 for w in profiles:
  print(ix,*w,count[w],good[w],useful[w],flush=True)
