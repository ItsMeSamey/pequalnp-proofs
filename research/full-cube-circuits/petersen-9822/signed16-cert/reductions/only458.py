"""Check every first-site allocation directly against the 1024 full target values."""
from itertools import product
from functools import cache
from collections import Counter
from audit_guard import truth,edges
@cache
def subs(m):return tuple(v for v in range(1024) if v&~m==0)
@cache
def rows(u):
 cols=subs(u);out={}
 for e in subs(1023^u):
  sig=sum(truth[e|w]<<j for j,w in enumerate(cols))
  piv=sum(i for i in (2,4) if i&u and any(truth[e|w]!=truth[e|w|i] for w in cols if not w&i))
  out[e]=(sig,piv)
 return out
@cache
def test(s,t,capacity,i):
 table=rows(1023^s^t)
 for e in subs(t):
  vals=set();pivs=set()
  for x in subs(s):
   sig,piv=table[e|x];vals.add(sig)
   if piv&i:pivs.add(sig)
   if len(vals)>capacity or len(pivs)>1:return False
 return True
def main():
 stats=Counter()
 for pattern in product(range(1,5),repeat=5):
  bs=[304,0,0,2,4]
  for v,j in zip([0,3,6,7,9],pattern):bs[j]|=1<<v
  r,a,b,q,o=bs
  if r&15 or r.bit_count()>3 or a&64 or b&128:continue
  if any(any(m>>x&m>>y&1 for x,y in edges) for m in bs[1:]):continue
  stats['placements']+=1;ever=False
  for order in ((1,2,3),(1,3,2),(2,1,3)):
   pref=0;guard=True;stats['orders']+=1
   for k,j in enumerate(order,1):
    block=bs[j]
    if not test(block,r|pref,2,0):break
    if j<3 and not test(block,r|pref,2,2**j):guard=False
    pref|=block
    if k>1 and not test(pref,r,2**k,0):break
   else:
    ever=True;stats['causal_orders']+=1
    if guard:stats['accepted']+=1;print('solution',bs,order)
  stats['causal_placements']+=ever
 print(stats)
 assert stats['accepted']==0 and stats['causal_orders']==9 and stats['causal_placements']==4
if __name__=='__main__':main()
