from collections import defaultdict,Counter
from functools import lru_cache
from itertools import combinations
from h5_raw_terminal import EDGES,target
N=[x for x in range(1024) if not target(x) and all(target(x|1<<i) for i in range(10) if not x>>i&1)]
def subs(mask):
 x=mask
 while True:
  yield x
  if not x:break
  x=(x-1)&mask
for mask in (0,1,0b1010,0b10010101,0b1000100010,1023):
 actual=list(subs(mask))
 expected={s for s in range(1024) if not s&~mask}
 assert len(actual)==1<<mask.bit_count() and set(actual)==expected
by=defaultdict(list)
for (i,I),(j,J) in combinations(enumerate(N),2):
 free=1023^(I|J)
 for x in subs(free):
  for y in subs(free):
   a=(J&~I)|x;b=(I&~J)|y
   if any(a&m and b&m for m in N) and any(a&e and b&e for e in EDGES):
    by[tuple(sorted((a,b)))].append((i,j))
counts=Counter()
exceptional=[]
for k,pairs in by.items():
 adj=[0]*16
 for i,j in pairs:adj[i]|=1<<j;adj[j]|=1<<i
 @lru_cache(None)
 def match(rem):
  if not rem:return 0
  b=rem&-rem;rest=rem^b
  v=match(rest);q=adj[b.bit_length()-1]&rest
  while q:
   h=q&-q;q^=h;v=max(v,1+match(rest^h))
  return v
 size=match(sum(1<<i for i,m in enumerate(adj) if m))
 counts[size]+=1
 if size>=4:exceptional.append((size,*k))
assert counts=={1:29850,2:4392,3:678,4:57,5:7,6:1}
assert [v for v in exceptional if v[0]==6]==[(6,68,130)]
assert (4,2,84) in exceptional
print(len(by),counts)
for row in sorted(exceptional): print(*row)
