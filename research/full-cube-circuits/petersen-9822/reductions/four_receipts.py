from collections import Counter
from itertools import permutations
from four_bins import V,subs,indep,bitcut,multicut,possible
def audit(r,o):
 stats=Counter()
 def step(p,d):
  i=o[d];t=p|r;mask=(V^t)&~4
  if i!=2:mask&=~2
  if i==0:mask&=~64
  if i==1:mask&=~128
  for b in subs(mask):
   s=b|p;u=V^r^s
   if i==2 and not b&2 or not indep(b):why='static'
   elif not bitcut(b,t,u):why='single'
   elif i<2 and not possible(b,t,u,2<<i):why='guard'
   elif d and not multicut(s,r,u,d+1):why='prefix'
   elif d==3 and not indep(u):why='output'
   elif d<3:why='advance';step(s,d+1)
   else:why='candidate'
   stats[d,why]+=1
 step(0,0);return stats
total=Counter()
for r in subs(304):
 if r.bit_count()>2:continue
 for o in permutations(range(4)):
  if o.index(0)>o.index(2):continue
  stats=audit(r,o);total.update(stats)
  print(r,''.join(map(str,o)),sorted(stats.items()))
assert not total[3,'candidate']
print('total',sorted(total.items()))
