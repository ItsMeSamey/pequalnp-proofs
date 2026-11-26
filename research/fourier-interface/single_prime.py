"""Check integral orbit correction support and its factorization modulo 2^s."""
from itertools import product
from math import comb
checks=0
for h in range(1,7):
 for R in range(1,h+1):
  for s in range(1,R+1):
   cap=(h-R+s-1)//2
   left,right={},{}
   for word in product(range(4),repeat=h):
    deg=sum(v!=0 for v in word)
    if deg>h-R: continue
    x=sum(1<<i for i,v in enumerate(word) if v in (1,3))
    y=sum(1<<i for i,v in enumerate(word) if v in (2,3))
    c=(-1)**deg*(-2)**word.count(3)%2**s
    if not c: continue
    assert x.bit_count()+y.bit_count()<=h-R+s-1
    if x.bit_count()<=cap: left.setdefault(x,[]).append((y,c))
    else:
     assert y.bit_count()<=cap
     right.setdefault(y,[]).append((x,c))
   assert len(left)+len(right)<=2*sum(comb(h,j) for j in range(cap+1))
   for x,y in product(range(1<<h),repeat=2):
    dist=(x^y).bit_count()
    target=sum((-1)**j*comb(dist,j) for j in range(min(h-R,dist)+1))
    if dist<=h-R: assert target==(x==y)
    actual=sum(c for a,z in left.items() if a&x==a for b,c in z if b&y==b)
    actual+=sum(c for b,z in right.items() if b&y==b for a,c in z if a&x==a)
    assert actual%2**s==target%2**s
   checks+=1
print(checks,"orbit factorizations checked entrywise")
