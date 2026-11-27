"""Necessary cofactor test for raw blocks of nine paid OR/NOT gates."""
from itertools import combinations
from functools import cache
from collections import Counter
N=10
ALL=(1<<N)-1
edges=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
f=[any((v>>a)&(v>>b)&1 for a,b in edges) for v in range(1<<N)]
def subsets(mask):
 a=mask
 while True:
  yield a
  if not a:return
  a=(a-1)&mask
@cache
def pair(U,x,y):
 X,Y=1<<x,1<<y
 W=ALL^(U|X|Y)
 for u in subsets(U):
  ok=15
  for w in subsets(W):
   a=u|w
   r0,rx,ry,rxy=f[a],f[a|X],f[a|Y],f[a|X|Y]
   # Primitive signal may be constant, x, y, or x OR y.
   ok &= ((int(r0==rx==ry==rxy)) | (int(r0==ry and rx==rxy)<<1)
          | (int(r0==rx and ry==rxy)<<2) | (int(rx==ry==rxy)<<3))
   if not ok:return False
 return True
@cache
def run(u,s,t,lo,firstmask):
 if (ALL^u).bit_count()>2*(9-s):return 0
 if s==9:return int(u==ALL and t==lo)
 total=0
 for neg in [False,True]:
  if s==0 and not neg:continue
  if t+neg>lo:continue
  avail=[i for i in range(N) if not u>>i&1]
  blocks=[()] if neg and t+1==lo else ([()] if s else [])+[(i,) for i in avail if s or firstmask>>i&1]
  if not neg:
   blocks+= [(i,j) for i,j in combinations(avail,2) if (i,j) not in edges and (j,i) not in edges and pair(u,i,j)]
  for block in blocks:
   total+=run(u|sum(1<<i for i in block),s+1,t+neg,lo,firstmask)
 return total
if __name__=='__main__':
 for t in (2,3,4):
  print(t,run(0,0,0,t,992),flush=True)
