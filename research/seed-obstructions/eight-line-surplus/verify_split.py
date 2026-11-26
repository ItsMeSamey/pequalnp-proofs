from pathlib import Path
from itertools import combinations
from sys import path
base=Path(__file__).resolve().parents[1]/'one-surplus';path.insert(0,str(base))
from verify_packing import samples
rows,_,t=samples(base/'L-meta-18968.json')
pos=[n for i,n in enumerate(rows) if t>>i&1];neg=[n for i,n in enumerate(rows) if not t>>i&1]
ls=[sum({n&8191 for n in pos if n>>(13+j)&1}) for j in range(7)]
count=0
for a,A in enumerate(ls):
 for b,B in enumerate(ls):
  if a==b:continue
  for p in range(13):
   if A>>p&1:continue
   for q in range(13):
    if not (B&~A)>>q&1:continue
    for k,v in combinations([i for i in range(7) if i not in (a,b)],2):
     assert any(n&(1<<(13+a)) and n&(1<<p) and n&(1<<q) and n&ls[k] and n&ls[v] for n in neg)
     count+=1
print(count,'marker plus two ordinary-neighborhood extensions')
count=0
for a,b in combinations(range(7),2):
 c=ls[a]&ls[b]
 for k,K in enumerate(ls):
  if k in (a,b):continue
  for p in range(13):
   if K>>p&1:continue
   for v,V in enumerate(ls):
    if v in (a,b,k):continue
    assert any(n&(1<<(13+k)) and n&(1<<p) and n&ls[a]&~c and n&ls[b]&~c and n&V for n in neg)
    count+=1
print(count,'punctured double-arm and exterior-resident extensions')
