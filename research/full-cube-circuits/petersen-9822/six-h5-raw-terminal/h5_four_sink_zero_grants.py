from itertools import combinations
from h5_raw_terminal import EDGES,target
N=[x for x in range(1024) if not target(x) and all(target(x|1<<i) for i in range(10) if not x>>i&1)]
def tr(x,S):return sum(1<<i for i,s in enumerate(S) if x&s)
r=[(tr(x,EDGES),tr(x,N)) for x in range(1024)]
unions=[0]*65536
for x in range(1,65536):
 b=x&-x;unions[x]=unions[x^b]|N[b.bit_length()-1]
def sub(mask):
 s=mask
 while True:
  yield s
  if s==0:break
  s=(s-1)&mask
assert all(sum((m&x)==m for x in N)>=2 for m in range(1,1024) if m.bit_count()<=2 and not target(m))
assert all(sum(bool(x&(1<<v)) for x in N)>2 for v in range(10))
for mask in (0,0b1010,0b1010010010):
 assert set(sub(mask))=={i for i in range(1024) if not i&~mask}
total=passed=0
for (i,I),(j,J) in combinations(enumerate(N),2):
 P=(1<<i)|(1<<j);outside=65535^P;terms=set()
 for n in sub(outside):
  a=1023^unions[n];b=1023^unions[outside^n]
  if r[a][1]&r[b][1]&P:terms.add(r[a][0]&r[b][0])
 maxterms=[s for s in terms if not any(s!=t and not s&~t for t in terms)]
 poses={0}
 for _ in range(4):poses|={z|t for z in poses for t in maxterms}
 free=1023^(I|J)
 for x in sub(free):
  for y in sub(free):
   a=(J&~I)|x;b=(I&~J)|y
   h=r[a][0]&r[b][0];hn=r[a][1]&r[b][1]
   if not(h and hn):continue
   total+=1;base=h&r[1023^unions[hn]][0]
   if any(z|base==8191 for z in poses):passed+=1
print(total,passed)

assert (total,passed)==(42761,0)
