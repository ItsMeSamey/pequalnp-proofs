from functools import lru_cache
from itertools import combinations
from collections import Counter
def audit(n):
 allones=(1<<(1<<(n+1)))-1
 raw=tuple(sum(1<<x for x in range(1<<(n+1)) if x>>j&1) for j in range(n+1))
 # Distinct leaf labels even for two H uses. An exterior with attachment sides
 # is an OR of its nonzero sides. Track their largest possible count directly.
 leaves=[(x,x) for x in raw[:-1]]+[(allones,0),(raw[-1],allones),(raw[-1],allones)]
 @lru_cache(None)
 def tree(bits):
  if bits&(bits-1)==0:
   z=leaves[bits.bit_length()-1];return {z:int(z!=(0,0))}
  out={}
  a=(bits-1)&bits
  while a:
   b=a^bits
   if a<b:
    for (p,q),u in tree(a).items():
     for (r,s),v in tree(b).items():
      z=(p|r,q|s);out[z]=max(out.get(z,0),u+v)
      z=(p&r,q&s);out[z]=max(out.get(z,0),int(z!=(0,0)))
   a=(a-1)&bits
  return out
 targets={}
 for optional in range(8):
  m=(((1<<n)-1)|(optional<<n))
  if not m:continue
  for z,parts in tree(m).items():targets[z]=max(parts,targets.get(z,0))
 states={frozenset([0,allones,*raw])};left=set(targets);fast=set()
 for step in range(n+2):
  for s in states:
   if step<=2:fast.update(s)
   for a in s:
    for b in s:left.discard((a,b))
  if not left or step==n+1:break
  states={s|{z} for s in states for a,b in combinations(s,2) for z in (a&b,a|b) if z not in s}
 assert len(left)==(12 if n==3 else 0)
 for f,j in left:
  z=1<<(1<<n)
  j0,j1=j%z,j//z
  assert j0==j1 and not ((f%z)&~j0 or j0&~(f//z))
  assert j in fast and targets[f,j]<=2
 print(n,len(targets),len(left),Counter(targets[z] for z in left))
for n in range(4):audit(n)
