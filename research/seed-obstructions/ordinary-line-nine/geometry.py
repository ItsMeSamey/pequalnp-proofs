from pathlib import Path
from itertools import combinations
import sys
seed=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(seed))
from verify_mixed import coords,target
stars=[sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
neg=[coords(i) for i in range(676) if not (target>>i)&1]
extras=[(a,b) for a in range(1,128) for b in range(a,128)]
good=lambda a,b:all(any(n&1<<i and l&a and l&b for n,l in neg) for i in range(13))
print('good slots by signatures (includes repeated singletons)',sum(good(a,b) for a,b in extras),'of',len(extras))
bad=[]
for t,s in enumerate(stars):
 for H in combinations(set(range(7))-{t},3):
  candidate=[n for n,l in neg if l&(1<<t) and all(n&stars[h] for h in H)]
  for x,y in combinations(range(13),2):
   pair=1<<x|1<<y
   if not pair&s and not any((n&pair)==pair for n in candidate):bad.append((t,H,pair))
print('failed extent',len(bad),'of',7*20*36,'first',bad[:5])
