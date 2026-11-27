from itertools import product
from functools import cache
from collections import Counter
from one_shared import bits,subs,neighbors,N,brute
V=1023
@cache
def bitcut(S,T,U):
 act=[(b,N[b]&U) for b in bits(S) if N[b]&U]
 if not act:return True
 k=act[0][1];a=sum(b for b,_ in act)
 return not(neighbors(S)&S or any(j!=k for _,j in act) or any(N[t]&S and a&~N[t] and k&~N[t] for t in bits(T)))
@cache
def multicut(S,T,U,k):
 for t in subs(T):
  h=neighbors(t)
  if h&t:continue
  live=U&~h; seen=set()
  for s in subs(S):
   key=-1 if (h|neighbors(s))&s else neighbors(s)&live
   seen.add(key)
   if len(seen)>1<<k:return False
 return True
if __name__=='__main__':
 ct=Counter();keys=Counter()
 for R in subs(V&~15):
  r=R.bit_count()
  if r>3:continue
  free=list(bits(V^R^6))
  for assignment in product(range(4),repeat=len(free)):
   bs=[0,0,2,4]
   for v,i in zip(free,assignment):bs[i]|=v
   if any(neighbors(w)&w for w in bs) or bs[0]&64 or bs[1]&128:continue
   ct[r,'raw']+=1;ok=[]
   for order in ((0,1,2),(1,0,2),(0,2,1)):
    S=0;good=True
    for level,i in enumerate(order,1):
     B=bs[i];earlier=R|S;S|=B;U=V^R^S
     if not bitcut(B,earlier,U) or (level>1 and not multicut(S,R,U,level)):
      good=False;break
    if good:ok.append(''.join(str(i) for i in order))
   if ok:
    keys[tuple(ok)]+=1;ct[r,'cut']+=1
    print('survivor',R,*bs,','.join(ok))
 print('counts',sorted(ct.items()),'orders',keys)
 pos=neg=0
 for s,t in ((1,0),(9,48),(3,48),(42,320),(12,0),(5,0)):
  u=V^s^t
  if s&t:continue
  expected=brute(s,t,u)
  assert bitcut(s,t,u)==multicut(s,t,u,1)==expected
  pos+=expected;neg+=not expected
 print('truth controls',pos,neg)
