from envelope import model as projected
from itertools import permutations
from pathlib import Path
from collections import Counter
import sys
from basic import model,stars,projective,positive,negative
def image(x,perm):return sum(((x>>j)&1)<<k for j,k in enumerate(perm))
labels=[sum(bool(s>>j&1)<<i for i,s in enumerate(stars)) for j in range(13)]
group=[]
for g in permutations(range(7)):
 moved=[image(a,g) for a in labels]
 if set(moved)!=set(labels):continue
 pts=[labels.index(y) for y in moved]
 assert {image(t,pts) for t in projective}==set(projective)
 def row(r):return image(r&8191,pts)|(image(r>>13,g)<<13)
 assert {row(r) for r in positive}==positive and {row(r) for r in negative}==negative
 group.append(g)
assert len(group)==24
results=Counter()
for size in (2,3):
 reps=Counter(min(image(m,g) for g in group) for m in range(128) if m.bit_count()==size)
 for e in sorted(reps):
  o=7-size
  for b in range(1+min(11-o,24-4*o)):
   check=model if b+o==11 else projected
   outcome,_=check(e,b,0,20000,1)
   print(e,size,b,outcome,flush=True)
   results[outcome]+=1
print(results)
assert results=={'UNSAT':55}
