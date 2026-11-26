from ast import literal_eval
from collections import Counter
from pathlib import Path
from itertools import combinations
from sys import path
path.insert(0,str(Path(__file__).resolve().parents[1]/'one-surplus'))
from verify_packing import samples
rows,_,target=samples(Path(__file__).resolve().parents[1]/'one-surplus'/'L-meta-18968.json')
pos=[r for i,r in enumerate(rows) if target>>i&1]
neg=[r for i,r in enumerate(rows) if not target>>i&1]
stars=[sum({p&8191 for p in pos if p>>(13+j)&1}) for j in range(7)]
assert all(s.bit_count()==4 for s in stars)
assert all((s&t).bit_count()==1 for s,t in combinations(stars,2))
for u,U in enumerate(stars):
 for t,T in enumerate(stars):
  if t==u: continue
  for v,V in enumerate(stars):
   if v in (t,u):continue
   for a,b in combinations([i for i in range(13) if not T>>i&1],2):
    X=(1<<a)|(1<<b)|(1<<(13+t))
    for q,r in combinations([i for i in range(13) if (U&~T)>>i&1],2):
     assert any(n&X==X and n&V and n&((1<<q)|(1<<r)) for n in neg)
counts=Counter()
for txt in open('geo-hard.txt'):
 z,x,y,a,b,i=literal_eval(txt)
 if len(a)>len(b):a,b=b,a
 assert len(a)==1 and 1<=len(b)<=2 and i is not None
 v=a[0]
 for w in b:
  assert v&~w and w&~v
  assert (v^w).bit_count()+len(b)-1<=5
 counts[len(b)]+=1
print('geometric cases covered',counts)
