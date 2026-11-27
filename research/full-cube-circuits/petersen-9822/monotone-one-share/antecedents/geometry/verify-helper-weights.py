import json,math,itertools
from fractions import Fraction as F
from pathlib import Path
E=[6,24,17,33,66,132,264,528,160,640,576,320,288]
# Determine all maximal independent sets directly.
Z=[s for s in range(1024) if all(s&e!=e for e in E) and all(any((s|1<<v)&e==e for e in E) for v in range(10) if not(s>>v&1))]
assert len(Z)==16
db={tuple(s):list(map(F,w)) for s,w in map(json.loads,Path('kw-helper.jsonl').read_text().splitlines())}
perm=(3,2,1,0,4,8,7,6,5,9)
def flip(s):return sum(1<<v for i,v in enumerate(perm) if s>>i&1)
w=db[(4,7,8)];db[4,5,6]=[w[16*E.index(flip(e))+Z.index(flip(z))] for e in E for z in Z]
keys={s for k in (2,3) for s in itertools.combinations(range(10),k)}
assert set(db)==keys
boundary=[]
for S,w in db.items():
 den=math.lcm(*(a.denominator for a in w));W=[int(den*a) for a in w]
 for L in [1<<i for i in range(10)]+[sum(1<<i for i in S)]:
  rows=[i for i,e in enumerate(E) if e&L];cs=[j for j,z in enumerate(Z) if not z&L]
  sums=[(0,)*len(cs)]
  for i in rows:
   new=[tuple(x+W[16*i+j] for x,j in zip(s,cs)) for s in sums]
   assert all(sum(max(0,x) for x in v)<=den for v in new)
   sums+=new
 target=19-len(S)
 assert sum(W)>=den*target
 if sum(W)==target*den:boundary.append(S)
assert set(boundary)=={(0,3),(0,9),(3,9),(0,3,9)}
print('165 raw OR labels verified; 161 strict; boundary',sorted(boundary))
