from itertools import combinations,product
from functools import lru_cache
raw=frozenset(1<<i for i in range(6))
def ops(S):
 return {z for a,b in combinations(S,2) for z in (a|b,a&b) if z and z not in S}
def states(R,h):
 seen=set()
 def dfs(S):
  while req:=ops(S)&(R-S): S=S|req
  if len(S-raw)+len(R-S)>h or S in seen:return
  seen.add(S)
  if R<=S:yield S
  if len(S-raw)+len(R-S)<h:
   for z in ops(S)-R:yield from dfs(S|{z})
 yield from dfs(raw)
def extra_pairs(S):
 # One OR and possibly another unary before or after. Need only exactly two;
 # take same OR twice to retain one.
 out=set()
 for a,b in product(S,repeat=2):
  out.add((a|b,63))
  out.add((a&b,b)) # (y OR a) AND b
  out.add((b,a|b)) # (y AND a) OR b
 return out
def check(stars):
 tri=[x for x in stars if x.bit_count()==3];D=[x for x in stars if x.bit_count()==2]
 assert len(tri)==3 and len(D)==2 and D[0]&D[1]==0
 ntested=0
 # At least one unary beyond the mandatory OR lies inside the cherry.
 for outside in (False,True):
  h=6-int(outside)
  for g in (range(1,63) if outside else [63]):
   # outside filter can affect any subset of ordinary stars and optionally both cherry leaves.
   for priv in product(*[[u for u in range(1,64) if u==s or u&g==s] for s in tri]):
    R=frozenset(priv)|({g} if outside else set())
    if not R.isdisjoint(raw) or len(R)>h:continue
    for S in states(R,h):
     ntested+=1
     for W in ({63,g} if outside else {63}):
      if any(d&W!=d for d in D):continue
      # Short branch is z OR v. The long branch has baseline a and active b.
      # After the cherry's common mask W, z has star a&W and y has b&v&W.
      for a,b in extra_pairs(S):
       for i in range(2):
        if a&W!=D[i]:continue
        for v in S:
         if a&v&W==0 and b&v&W==D[1-i]:return S
 # Two internal extras, no exterior filters leave only five hot gates.
 assert not any(states(frozenset(tri),5))
 return ntested
p=[v for v in range(1,8) if v!=1]
l=[v for v in range(1,8) if v!=2]
for a,b in ((p,l),(l,p)):
 stars=[sum(1<<j for j,y in enumerate(b) if (x&y).bit_count()%2==0) for x in a]
 for d,s in enumerate(stars):
  if s.bit_count()==3:
   count=check(stars[:d]+stars[d+1:])
   assert count==27
   print(d,count,"infeasible hot states")
