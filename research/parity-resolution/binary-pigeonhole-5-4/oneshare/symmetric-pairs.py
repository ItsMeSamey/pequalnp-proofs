from pathlib import Path
from itertools import permutations
exec(Path(__file__).with_name('natural-pairs.py').read_text().split('seen=set()')[0].replace('def status(w,I):return reduce(xor,(w[j] for j in I),0)==0','def status(w,I):return all(reduce(xor,(w[j] for j in range(5) if mask>>j&1),0)==0 for mask in I)'))
subs={frozenset([0])}
for z in range(1,32):
 if z.bit_count()%2==0:subs.update(s|{i^z for i in s} for s in tuple(subs))
subs.discard(frozenset([0]))
ps=list(permutations(range(5)))
def word(p,z):return sum(1<<p[i] for i in range(5) if z>>i&1)
im={s:[frozenset(word(p,z) for z in s) for p in ps] for s in subs}
seen=set();best=1000
for s in subs:
 for t in subs:
  if s==t or (s,t) in seen:continue
  seen.update(zip(im[s],im[t]))
  c=[region(s,t,r) for r in range(3)]
  m=sum(4*a+b for a,b in c)+41+(4 if len(s)==2 and max(s).bit_count()==2 else 0)
  print(sorted(s),sorted(t),c,m,flush=True)
