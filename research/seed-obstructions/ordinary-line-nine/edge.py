from missing import *
from itertools import product
from functools import lru_cache

pairs=[[lines[t]&points[x] for x in inside(8191^ss[t])] for t in range(7)]
def analyze(a,b):
 edge=failures(a,b)
 if len(edge)!=1:return
 t,u=edge[0]
 sig=[(bool(a&(1<<j)),bool(b&(1<<j))) for j in range(7)]
 active=[(lc[a] if x else alln)&(lc[b] if y else alln) for x,y in sig]
 safe=[sum(1<<p for p in inside(s) if points[p]&active[j]) for j,s in enumerate(ss)]
 hit=[pc[s] for s in safe]
 extra=[(s^z).bit_count() for s,z in zip(ss,safe)]
 outside=[i for i in range(7) if i not in (t,u)]
 missing=[x for x,y in [(t,u),(u,t)] if not all(m&active[y]&hit[y] for m in pairs[x])]
 for j in outside:
  labels=[x for x in outside if x!=j]
  witnesses=[hit[v] for v in labels]+[hit[t]|hit[u]]
  witnesses += [hit[v] & (hit[t]|hit[u]) for v in labels]
  witnesses += [hit[v]&hit[w] for v,w in combinations(labels,2) if sig[v]!=sig[w]]
  if not all(all(m&g for m in pairs[j]) for g in witnesses):
   return 'ordinary fail'
 n=sum(extra)+sum(3-extra[x] for x in missing)
 cost=(a|b).bit_count()-2+bool(a&b)
 # In one branch with no exceptional split, all seven targets remain.
 # In the exceptional branch both opposite-child cofactors are single-use
 # and two simultaneously retained extra cofactors must serve outside targets.
 def excess(scope):
  return max((max(min(e,8-e-extra[i]-extra[j]) for e in range(12)) for i,j in product(scope,repeat=2)
              if sig[i]==(1,0) and sig[j]==(0,1)),default=0)
 return ('all' if n+excess(outside)<=cost+2 else 'distinct' if n<=cost+2 else 'budget',n,excess(outside),n+excess(range(7))<=cost+2)
if __name__=='__main__':
 C=Counter()
 for a,b in combinations([s for s in range(1,128) if s.bit_count()>=2],2):
  result=analyze(a,b)
  if result is None:continue
  c=(a|b).bit_count()-2+bool(a&b)
  C[c,result if isinstance(result,str) else (result[0],result[-1])]+=1
 for c in range(2,7):print(c,{k:v for (n,k),v in C.items() if n==c})
