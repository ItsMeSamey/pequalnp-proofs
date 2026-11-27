from pathlib import Path
from itertools import combinations, product
from functools import cache,reduce
from operator import xor
exec((Path(__file__).parents[1]/'cdcl/treecost.py').read_text().split("print('optimum")[0])
E=list(combinations(range(5),2))
def status(w,I):return reduce(xor,(w[j] for j in I),0)==0
def labels(w):return sum(1<<(4*j+w[a]) for j,(a,b) in enumerate(E) if w[a]==w[b])
@cache
def tau(C):
 if not C:return 0
 z=min(C,key=int.bit_count)
 return 1+min(tau(tuple(c for c in C if not(c>>i&1))) for i in range(40) if z>>i&1)
def region(I,J,r):
 def good(w):return (0 if status(w,I) else 1 if status(w,J) else 2)==r
 dom=[labels(w) for w in product(range(4),repeat=5) if good(w)]
 g=0
 for z in dom:
  if z.bit_count()==1:g|=z
 need=sorted({z for z in dom if not(z&g)}, key=int.bit_count)
 minimal=[]
 for z in need:
  if all(z&t!=t for t in minimal):minimal.append(z)
 p=sum(1<<j for j,w in enumerate(R) if good(w))
 return (opt(p,25) if p else 0),tau(tuple(minimal))
seen=set()
for ni,nj in product((2,4),repeat=2):
 for I in combinations(range(5),ni):
  for J in combinations(range(5),nj):
   tag=ni,nj,len(set(I)&set(J))
   if tag in seen or I==J:continue
   seen.add(tag)
   c=[region(I,J,r) for r in range(3)]
   p=sum(4*a+b for a,b in c)
   print(tag,c,p,p+41,flush=True)
