from collections import Counter
from itertools import combinations
from pathlib import Path
from sys import path
base=Path(__file__).resolve().parents[1]/'one-surplus'
path.insert(0,str(base))
from verify_packing import samples
rows,_,target=samples(base/'L-meta-18968.json')
neg=[n for i,n in enumerate(rows) if not target>>i&1]
pos=[n for i,n in enumerate(rows) if target>>i&1]
stars=[sum({n&8191 for n in pos if n>>(13+j)&1}) for j in range(7)]
assert all(s.bit_count()==4 for s in stars)
assert all((s&t).bit_count()==1 for s,t in combinations(stars,2))
hist=Counter()
for t,T in enumerate(stars):
 for u,U in enumerate(stars):
  if u==t:continue
  for a,b in combinations([i for i in range(13) if not T>>i&1],2):
   X=(1<<a)|(1<<b)|(1<<(13+t))
   bank=[n for n in neg if n&X==X]
   marks=[q for q in range(13) if (U&~T)>>q&1]
   good=sum(all(any(n&(1<<q) and n&V for n in bank) for v,V in enumerate(stars) if v not in (t,u)) for q in marks)
   assert good>=2
   hist[good]+=1
print('universally usable exclusive points:',dict(hist))
