from pathlib import Path
from itertools import combinations_with_replacement
from collections import Counter
p=Path(__file__).resolve().parent
forms=set()
for cols in combinations_with_replacement([(0,0),(0,1),(1,0),(1,1),(1,2)],6):
 for dep in [0,4,12]:
  def build(c,d):return (d+sum(a<<(4+2*j) for j,(a,b) in enumerate(c)),sum(b<<(4+2*j) for j,(a,b) in enumerate(c)))
  t=build(cols,dep)
  if not all(t) or dep==12 and (1,2) in cols:continue
  if not dep:t=min(t,build(sorted((1,2) if b==2 else (b,a) for a,b in cols),0))
  forms.add(t)
forms=sorted(forms);assert len(forms)==403
print('widths',Counter(a.bit_count() for a,b in forms))
for w,src,pattern in [(1,'fast1.out','library1.out'),(1,'fast1.out','library1-straddle.out'),(2,'fast2.out','library2.out'),(3,'anchors3.out','library3.out')]:
 lines=[s.split() for s in (p/src).read_text().splitlines()]
 roots={(int(s[1]),int(s[2])) for s in lines if s[0]=='root'}
 profiles={int(s[1]):list(map(int,s[2:])) for s in lines if s[0]=='profile'}
 assert set(profiles)=={i for i,(a,b) in enumerate(forms) if a.bit_count()==w}
 for i,(a,b,r,c) in profiles.items():assert (a,b)==forms[i] and c==sum(j==i for j,k in roots)
 rows=[list(map(int,l.split())) for f in p.glob(pattern) for l in f.read_text().splitlines()]
 assert len(rows)==len(roots) and {tuple(r[:2]) for r in rows}==roots and all(not r[-1] for r in rows)
 print(w,len(profiles),sum(r[2] for r in profiles.values()),len(rows),sum(r[2] for r in rows),sum(r[3] for r in rows))
for w,name in [(4,'width4.out'),(4,'width4-parity-free.out'),(3,'width3-three-outside.out')]:
 rows=[list(map(int,l.split())) for l in (p/name).read_text().splitlines()]
 assert {r[0] for r in rows}=={i for i,(a,b) in enumerate(forms) if a.bit_count()==w}
 assert all(tuple(r[1:3])==forms[r[0]] and not r[-1] for r in rows)
 print(name,len(rows),*[sum(r[k] for r in rows) for k in [3,4,5]])
