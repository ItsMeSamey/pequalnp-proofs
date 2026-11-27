from itertools import permutations
from functools import cache
from three_bins import bitcut,multicut,subs,neighbors
from guard_test import possible
V=1023
@cache
def indep(s):return not(neighbors(s)&s)
def solve(r,order):
 c=0
 def visit(pref,d,prior):
  nonlocal c
  j=order[d];t=r|pref;allowed=(V^t)&~4
  if j!=2:allowed&=~2
  if j==0:allowed&=~64
  if j==1:allowed&=~128
  for b in subs(allowed):
   if j==2 and not b&2 or not indep(b):continue
   s=pref|b;u=V^r^s
   if not bitcut(b,t,u) or j<2 and not possible(b,t,u,2<<j):continue
   if d and not multicut(s,r,u,d+1):continue
   if d<3:visit(s,d+1,prior+(b,));continue
   if not indep(u):continue
   c+=1;bs=dict(zip(order,prior+(b,)))
   print('pass',r,''.join(map(str,order)),*(bs[k] for k in range(4)),u)
 visit(0,0,())
 return c
if __name__=='__main__':
 total=0
 for r in subs(304):
  if r.bit_count()>2:continue
  for order in permutations(range(4)):
   if order.index(0)>order.index(2):continue
   c=solve(r,order);total+=c;print('done',r,''.join(map(str,order)),c,flush=True)
 print('TOTAL',total)
