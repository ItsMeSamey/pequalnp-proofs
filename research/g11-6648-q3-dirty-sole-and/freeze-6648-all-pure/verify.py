from itertools import combinations
from functools import lru_cache
from collections import Counter
edges=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
ambient=edges+[(3,6),(3,7)]
N=[sum(1<<(v if u==i else u) for u,v in ambient if i in (u,v)) for i in range(11)]
full=2047
mi=[s for s in range(2048) if all(not(s>>u&1 and s>>v&1) for u,v in ambient) and all(s>>v&1 or s&N[v] for v in range(11))]
cores=[((1<<u)|(1<<v)) for u,v in edges]; covers={s:sum(1<<i for i,e in enumerate(cores) if e&s) for s in range(2048)}
rejs={s:sum(1<<i for i,I in enumerate(mi) if not s&I) for s in range(2048)}
# Realized nonsingleton supports in centreless primitive clauses have x absent.
# The only nontrivial access to 6,7 is via {6,9}, {7,10}, or {6,7,w}.
# For stronger lower bounds narrow primitive eligibility on actual, unshrunk clauses.
def allowed(s):
 if s&(1<<3):return False
 if s&(1<<6) and not(s&(1<<9) or (s&(1<<7) and s&sum(1<<i for i in (0,1,2,4,5,8,9,10)))):return False
 if s&(1<<7) and not(s&(1<<10) or (s&(1<<6) and s&sum(1<<i for i in (0,1,2,4,5,8,9,10)))):return False
 return True
# h has no centreless AND reader; E the only non-A reader.
valid=[s for s in range(1,2048) if allowed(s) and rejs[s]]
whole=(1<<len(mi))-1
def score(R):
 options={}; forbidden=[sum(1<<(v if u==i else u) for j,(u,v) in enumerate(edges) if R>>j&1 and i in (u,v)) for i in range(11)]
 anchors=[N[i]&~forbidden[i]&~((1<<3)|(1<<6)|(1<<7)) for i in range(11) if i not in (3,6,7)]
 for s in valid:
  if R&~covers[s]:continue
  cost=1 if s.bit_count()==1 or any(not s&~a for a in anchors) else 2
  h=rejs[s];options[h]=min(options.get(h,100),cost)
 opts=sorted(options.items(),key=lambda p:(p[1],-p[0].bit_count()));keep=[]
 for h,c in opts:
  if not any(c>=d and h|k==k for k,d in keep):keep.append((h,c))
 by=[[p for p in keep if p[0]>>i&1] for i in range(len(mi))]
 @lru_cache(None)
 def dp(m):
  if not m:return 0
  choices=min((ops for i,ops in enumerate(by) if m>>i&1),key=len)
  return min((c+dp(m&~h) for h,c in choices),default=100)
 return dp(whole)
if __name__=='__main__':
 bad=[]
 for R in range(1,1<<len(edges)):
  f=score(R)
  if f<R.bit_count():bad.append((R,R.bit_count(),f))
 print('checked', (1<<len(edges))-1, 'edge families; deficient records', bad)
 assert bad==[(8520,4,3)]
