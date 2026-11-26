from itertools import combinations,product
from fractions import Fraction as Q
# Generic signed OR: three terminals and a center. Externally used third terminal also doubles.
mon=[0,0,Q(3,2),1]
edge={(0,1):1,(0,2):Q(-1,2),(1,2):Q(-1,2),(0,3):1,(1,3):1,(2,3):Q(-1,2)}
def terms(left):
 if not left:return [1]
 v,*tail=left
 return [mon[v]*w for w in terms(tail) if mon[v]*w]+[edge[v,u]*w for u in tail for w in terms([s for s in tail if s!=u]) if edge[v,u]*w]
for mask in range(8):
 S=[i for i in range(3) if mask>>i&1]; a=[2*w for w in terms(S+[3])]
 assert all(w==int(w) for w in a) and sum(a)==2*(mask!=7)
 if 2 in S and mask!=7:assert sorted(a)==[-1,3]
for t in range(1,5):
 # Consecutive triples (2i,2i+1,2i+2) each forbid its seven nonzero words.
 sol=0;badport=0
 for i in range(t):
  for f in product([0,1],repeat=3):
   if any(f): badport+=min(f)==0
 for x in product([0,1],repeat=2*t+1):
  sol+=all(not any(x[2*i:2*i+3]) for i in range(t))
 assert sol==1 and badport==6*t
P=[2,3,5,7,11,13,17,19,23]
count=0
for s in range(1,4):
 for S in combinations(range(16),s):
  assert any(sum(sum((x>>j&1)*(2**j%p) for j in range(4))==sum((S[0]>>j&1)*(2**j%p) for j in range(4)) for x in S)==1 for p in P[:4*(s-1)+1])
  count+=1
print('8 exact OR fibers, four connected unique-model controls and',count,'sparse model families checked')
