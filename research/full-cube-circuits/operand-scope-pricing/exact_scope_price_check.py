from itertools import combinations
from functools import cache
sets=[s for s in range(1,16) if s.bit_count()>1]
cost={0:0}
for mask in range(1<<len(sets)):
 if mask not in cost:continue
 avail={1,2,4,8}|{v for i,v in enumerate(sets) if mask>>i&1}
 for i,s in enumerate(sets):
  if s not in avail and any(a|b==s for a,b in combinations(avail,2)):
   cost[mask|1<<i]=mask.bit_count()+1
@cache
def private_price(s,m):
 avail={1,2,4,8}|{v for i,v in enumerate(sets) if m>>i&1}
 dp={0:0}
 for v in avail:
  if v&s==v:
   for x,k in list(dp.items()):dp[x|v]=min(dp.get(x|v,99),k+1)
 return dp[s]-1
for t in range(1<<len(sets)):
 targets=[s for i,s in enumerate(sets) if t>>i&1]
 opt=min(c for m,c in cost.items() if m&t==t)
 allowed=sum(1<<i for i,s in enumerate(sets) if sum(v&s==s for v in targets)>=2)
 result=min(c+sum(private_price(s,m) for s in targets) for m,c in cost.items() if not m&~allowed)
 assert result==opt
print('2048 four-source target families passed unrestricted binary-merge comparison')
