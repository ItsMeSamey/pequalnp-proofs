from collections import defaultdict
from itertools import combinations
from functools import lru_cache
R=defaultdict(set)
for line in open('less4'):
 x,y=map(int,line.split());R[x].add(y);R[y].add(x)
vals=list(R)
def mins(s):return [i for i in range(16) if s>>i&1 and all(not(s>>(i^(1<<j))&1) for j in range(4) if i>>j&1)]
def up(z):return sum(1<<i for i in range(32) if any(i%16&x==x for x in z))
@lru_cache(None)
def fit(lo,hi):return {x for x in vals if x&lo==lo and x&hi==x}
cases=set();hard=set()
for ln in open('jointf.txt'):
 n,z,a,b,m=map(int,ln.split())
 if n!=4 or b in R[a] or a&b in (a,b):continue
 for i in mins(a&b):
  ax=mins(a&~b);bx=mins(b&~a)
  for k in range(1,min(len(ax),2)+1):
   for aa in combinations(ax,k):
    for l in range(1,min(len(bx),2)+1):
     for bb in combinations(bx,l):
      case=(a,b,aa,bb,i);cases.add(case)
      ah=sum(1<<x for x in range(32) if any(a>>(x|w)&1 for w in bb)); bh=sum(1<<x for x in range(32) if any(b>>(x|w)&1 for w in aa))
      if not any(R[h]&fit(up((*bb,i)),bh) for h in fit(up((*aa,i)),ah)):hard.add(case)
print(len(cases),len(hard))
for row in sorted(hard)[:12]:print(row)
open('joint-hard','w').write('\n'.join(map(repr,sorted(hard))))
