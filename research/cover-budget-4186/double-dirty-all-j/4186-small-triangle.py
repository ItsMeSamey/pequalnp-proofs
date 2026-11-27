from itertools import product
from collections import Counter
left=[]
for x,y,w,i,j,k in product(range(2,8),range(2,8),range(1,8),range(6),range(6),range(6)):
 N=x+y+w+i+j+k
 if N>=10:continue
 F=(x+w+i,y+w+j,x+y+k)
 # coupled slots count via common tree. x=01 vertices A and E, y=B,E; w=A,B.
 shares=((0,w,x),(w,0,y),(x,y,0))
 for r in product(range(3),repeat=3):
  if any(2**a>b for a,b in zip(r,F)):continue
  deficit=2*sum(r)-N-2
  if deficit<=0:continue
  gain=0
  for h in range(3):
   if r[h]!=2:continue
   # ternary choices for which shared blocks can guarantee exact clause via capacity.
   # every size-L root has at most 2(L-4) occurrences not uniquely rejecting.
   b=2*(F[h]-4)
   for minimum in (1,2):
    if sum(shares[h][z] for z in range(3) if r[z]>=minimum)>b:gain=max(gain,minimum)
  if gain<deficit:left.append((x,y,w,i,j,k,r,F,deficit,gain))
print('len',len(left))
for x,y,w,i,j,k,r,F,deficit,gain in left:
 shares=((0,w,x),(w,0,y),(x,y,0))
 impossible=any(F[h]==4 and r[h]==2 and r[z]==2 and shares[h][z]>=2
                for h in range(3) for z in range(3))
 assert impossible, (x,y,w,i,j,k,r)
 print((x,y,w,i,j,k),r,F,deficit,gain,"two shared tight occurrences")
print("surviving profiles: 0")
