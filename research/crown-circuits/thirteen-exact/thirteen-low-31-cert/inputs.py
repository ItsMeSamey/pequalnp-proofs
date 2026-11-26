from pathlib import Path
from itertools import permutations,product
from collections import Counter
def enumerate_four():
 A=4;D=16;F=(1<<D)-1
 half=[sum(1<<x for x in range(D) if x>>i&1) for i in range(A)]
 seen=set();out=[]
 def rec(u,b):
  if len(u)==4:
   atoms={tuple(x>>j&1 for x in b) for j in range(16)}
   if len(atoms)<13:return
   key=min(tuple(transform(u[P.index(j)]) for j in range(A)) for P,transform in group)
   if key not in seen:seen.add(key);out.append(u)
   return
  opts={0}
  for x in b:opts.update(v|x for v in list(opts))
  opts.add(F);j=len(u)
  for a in sorted(opts-{0}):rec(u+[a],b+[a&half[j],a&(F^half[j])])
 group=[]
 for P in permutations(range(A)):
  for f in range(D):
   to=[sum((((v^f)>>j&1)<<P[j]) for j in range(A)) for v in range(D)]
   def trans(m,T=to):return sum((1<<k) for j,k in enumerate(T) if m>>j&1)
   group.append((P,trans))
 rec([],[]);return out
s=Path(__file__).resolve().parent
a4=enumerate_four()
a5=[list(map(int,x.split())) for x in (s/'five-universe.txt').read_text().splitlines()]
for a,rows in [(4,a4),(5,a5)]:
 D=1<<a; F=(1<<D)-1
 H=[sum(1<<p for p in range(D) if p>>i&1) for i in range(a)]; out=[];allr=[];counts=Counter()
 for i,u in enumerate(rows):
  B=[v&h for j,v in enumerate(u) for h in (H[j],F^H[j])];atoms=[F]
  for b in B:atoms=[y for x in atoms for y in (x&b,x&~b) if y]
  if len(atoms)<13:continue
  q=6-len(set(u)-set(B)-{F}); sparse=any(sum(not (v&x) for x in atoms)<=2 for v in set(u)-{F})
  counts[q,sparse]+=1;allr.append([i,*u])
  if not sparse:out.append([i,*u])
 for name,rr in [('all',allr),('hard',out)]:(s/f'{name}{a}.txt').write_text(''.join(' '.join(map(str,r))+'\n' for r in rr))
 print(a,len(allr),len(out),sorted(counts.items()))
