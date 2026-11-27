from itertools import permutations
from functools import cache
from collections import Counter
w=sorted(set(permutations((0,0,1,2,3))))
rows=[sum(x<<(2*i) for i,x in enumerate(t)) for t in w]
labels={tuple(i for i,x in enumerate(t) if not x) for t in w}
ls=[sum(1<<i for i,t in enumerate(w) if all(t[j]==0 for j in a)) for a in labels]
full=(1<<60)-1
qs={min(s,full^s) for q in range(1,1024) for s in [sum(((q&x).bit_count()%2)<<i for i,x in enumerate(rows))]}-{0}
@cache
def cost(s):return sum(bool(l&s) for l in ls)
@cache
def possible(s,b):
 if cost(s)>b:return False
 if cost(s)<=1:return True
 for u in {min(s&q,s^(s&q)) for q in qs}-{0}:
  v=s^u
  for c in range(cost(u),b-cost(v)+1):
   if possible(u,c) and possible(v,b-c):return True
 return False
print(len(qs),Counter(cost(q)+cost(full^q) for q in qs),flush=True)
for b in (24,25):
 print(b,possible(full,b),flush=True)
