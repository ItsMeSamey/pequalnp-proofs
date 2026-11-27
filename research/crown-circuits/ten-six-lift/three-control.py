from itertools import combinations
from pathlib import Path
from random import Random
random=Random(23189)
def accepts(mask,targets):
 v=[bool(mask>>i&1) for i in range(12)]
 for j,t in enumerate(targets,3):
  if v[2*j] and v[2*j+1]:
   for i in range(12):v[i]|=bool(t>>i&1)
 return any(v[2*j] and v[2*j+1] for j in range(3))
def blocked(z,targets):
 b=sum(1<<(2*j+((z>>j)&1)) for j in range(3))
 for j in (5,4,3):
  if b&targets[j-3]:b|=1<<(2*j+((z>>j)&1))
 return b
target=(5,18,34);receiver=(192,768,3072,9)
for x in range(16):
 m=0
 for i,r in enumerate(receiver):
  if x>>i&1:m|=r
 assert accepts(m,target)==(x.bit_count()>=2)
for t in random.sample(Path(__file__).with_name('t8-three-profiles.tsv').read_text().splitlines(),100):
 T=tuple(map(int,t.split())); B=[blocked(z,T) for z in range(64)]
 for i in range(20):
  m=random.randrange(4096)
  assert not accepts(m,T)==any(not m&k for k in B)
print('16 full control states; 2000 semantic certificate checks')
