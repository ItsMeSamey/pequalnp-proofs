from random import Random
from itertools import combinations
rng=Random(123)
def solve(mat,lp,rq):
 out=[]
 n=len(lp);m=len(rq)
 for x in range(1,1<<n):
  pl=[i for i in range(n) if x>>i&1]
  p=sum(lp[i]>=0 for i in pl)
  if p%2==0:continue
  r=sum(lp[i]==1 for i in pl)%2
  cand=[j for j in range(m) if not (sum(mat[i]>>j&1 for i in pl)%2)]
  # y must be supported on cand, label=(1,r), and mat[x]y=0.
  fac=0
  for j in cand:
   v=(1<<len(pl))|(rq[j]<<(len(pl)+1))|sum(((mat[i]>>j)&1)<<h for h,i in enumerate(pl))
   fac |= 0
   if j==cand[0]: piv={}
   while v:
    k=v.bit_length()
    if k not in piv:piv[k]=v;break
    v^=piv[k]
  if not cand:continue
  goal=((r*2+1)<<len(pl))
  while goal and goal.bit_length() in piv:goal^=piv[goal.bit_length()]
  if not goal:
   out.append(x)
   if len({lp[i] for i in pl if lp[i]>=0})==1:return True
 return out and (mat,lp,rq,out)

from functools import reduce
for it in range(2000):
 n=rng.choice([1,3]);m=rng.choice([2,4]);z=rng.randrange(2,7);u=rng.choice([1,3,5]);v=rng.choice([2,4,6])
 lp=[0]*n+[1]*m+[-1]*z
 rq=[0]*u+[1]*v
 mat=[]
 for a in lp[:-1]:
  row=sum((a==b or rng.getrandbits(1))<<j for j,b in enumerate(rq))
  if row.bit_count()%2:row^=1<<next(j for j,b in enumerate(rq) if a!=b)
  mat.append(row)
 mat.append(reduce(int.__xor__,mat))
 Z=mat[n+m:]
 mask=(1<<u)-1
 t=[(row&mask).bit_count()%2 for row in Z]
 E=reduce(int.__xor__,Z,0)
 T=reduce(int.__xor__,[row for row,h in zip(Z,t) if h],0)
 val=0
 for i,pr in enumerate(lp[:n+m]):
  own=mask if not pr else (((1<<(u+v))-1)^mask)
  other=((1<<(u+v))-1)^own
  for row in Z:
   val+=(own&row).bit_count()*(mat[i]&other&row).bit_count()*(other&~mat[i]&~row).bit_count()
 assert val%2==1^(int.bit_count(T&E)%2)
 if not solve(mat[:n]+mat[n+m:],lp[:n]+lp[n+m:],rq) and not solve(mat[n:],lp[n:],rq):
  print(it,mat,lp,rq,flush=True);break
else:print('all pass')
