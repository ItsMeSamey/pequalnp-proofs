"""Finite matching augmentation census for the complement of the eight-cycle."""
from itertools import combinations
base=[(i,j) for i,j in combinations(range(8),2) if j-i not in (1,7)]
qualified=0
subsets=sorted([s for s in range(1,1023) if s.bit_count()%2==0],key=int.bit_count)
def test(r):
 candidates=[1<<i|1<<j for i,j in combinations(range(10),2) if not r[i]>>j&1]
 for s in subsets:
  if all((v&s).bit_count()%2 for i,v in enumerate(r) if s>>i&1):
   candidates=[m for m in candidates if s&m!=m]
   if not candidates:return []
 return candidates
for rsize in (2,3,4):
 for m in combinations(base,rsize):
  ends=sum(([i,j] for i,j in m),[])
  if len(set(ends))!=len(ends):continue
  for flags in range(1<<(len(ends)-1)): # mod swap 8,9: final endpoint goes to 8
   for direct in (0,1):
    if not all(v in (3,5) for v in (flags.bit_count()+direct, len(ends)-flags.bit_count()+direct)):continue
    r=[0]*10
    for i,j in base:
     if (i,j) not in m:r[i]|=1<<j;r[j]|=1<<i
    for k,i in enumerate(ends):
     j=8+(flags>>k&1)
     r[i]|=1<<j;r[j]|=1<<i
    if direct:r[8]|=512;r[9]|=256
    qualified+=1
    # Check all old/new pin positions; a positive reports the full physical array.
    pairs=test(r)
    assert not pairs,(r,pairs)
assert qualified==7251
print(qualified,'matching augmentations, all pin pairs have a proper witness')

from odd_pair_square_multiplicity_check import graph,supports
for r in (graph(8,base),[220,224,49,97,229,158,155,115]):
 assert list(supports(r,3))==[255]
 for i,j in combinations(range(8),2):
  allowed=255 ^ (1<<i) ^ (1<<j)
  seen=allowed & -allowed
  while True:
   nxt=seen
   for k in range(8):
    if seen>>k&1:nxt |= r[k]&allowed
   if nxt==seen:break
   seen=nxt
  assert seen==allowed
print("two order-eight controls: 28 deletions and all raw supports checked for each")
