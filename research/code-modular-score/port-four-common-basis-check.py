from itertools import combinations,combinations_with_replacement
planes=sorted({1|(1<<a)|(1<<b)|(1<<(a^b)) for a in range(1,16) for b in range(1,a)})
u=planes[0]; complements=[x for x in planes if x&u==1]
pairs=list(combinations_with_replacement(complements,2))
obs=[sum(1<<i for i,(v,w) in enumerate(pairs) if p&v==p&w==1) for p in planes if p!=u]
allbits=(1<<len(pairs))-1
def search(left,candidates,k):
 if not left:return []
 if not k:return None
 candidates=[e for e in candidates if left&obs[e]]
 if sum(sorted(((left&obs[e]).bit_count() for e in candidates),reverse=True)[:k])<left.bit_count():return None
 inds=[i for i in range(len(pairs)) if left>>i&1]
 options=min(([e for e in candidates if obs[e]>>i&1] for i in inds),key=len)
 banned=set()
 for e in options:
  res=search(left&~obs[e],[c for c in candidates if c!=e and c not in banned],k-1)
  if res is not None:return [e]+res
  banned.add(e)
for k in range(1,15):
 res=search(allbits,list(range(34)),k)
 print(k,res,flush=True)
 if res is not None:break
