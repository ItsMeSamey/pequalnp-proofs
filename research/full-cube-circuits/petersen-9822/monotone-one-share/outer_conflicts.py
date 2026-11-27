from pathlib import Path
from graph import E,Z,V
from collections import Counter
full=(1<<1024)-1
up=[sum(1<<m for m in range(1024) if m&e==e) for e in E]
dn=[sum(1<<m for m in range(1024) if m&z==m) for z in Z]
F=0
for v in up:F|=v
mask0={1<<i:sum(1<<m for m in range(1024) if not m>>i&1) for i in range(10)}
def cover(edges):
 if not edges:return 0
 return 1+min(cover([q for q in edges if i not in q]) for i in edges[0])
def price(code,mandatory):
 pos0=neg1=0
 for i,x in enumerate(up):
  if not code>>i&1:pos0|=x
 for i,x in enumerate(dn):
  if not code>>(13+i)&1:neg1|=x
 tests=((pos0,full^F),(F,neg1));bad=[]
 for x in mask0:
  if any(n&mask0[x]&(p>>x) for p,n in tests):mandatory|=x
  for y in mask0:
   if y<=x:continue
   low=mask0[x]&mask0[y]
   both=any(low&(p>>(x+y))&(n>>x)&(n>>y) for p,n in tests)
   either=any(low&n&(p>>x)&(p>>y) for p,n in tests)
   if both and either:bad.append((x,y));mandatory|=x|y
 return 2+mandatory.bit_count()+cover(bad)
