from pathlib import Path
from three_bins import V,subs,neighbors,N
from functools import cache
from collections import Counter
@cache
def possible(S,T,U,i):
 assert i&U
 for t in subs(T):
  if neighbors(t)&t:continue
  seen=set()
  for s in subs(S):
   if neighbors(s|t)&(s|t):continue
   q=neighbors(s|t)&U
   if q&i or N[i]&U&~q:
    seen.add(q)
    if len(seen)>1:return False
 return True
ct=Counter()
for line in Path('three_bins.log').read_text().splitlines():
 if not line.startswith('survivor '):continue
 _,r,a,b,q,o,orders=line.split();R,*B=map(int,(r,a,b,q,o));out=[]
 for order in orders.split(','):
  prior=R
  for j in map(int,order):
   rest=V^(prior|B[j])
   if j<2 and not possible(B[j],prior,rest,2<<j):break
   prior|=B[j]
  else:out.append(order)
 if out:
  ct[tuple(out)]+=1;print('survivor',R,*B,','.join(out))
print('survivors',sum(ct.values()),ct)
