"""Independent local arithmetic checks for the two-copy proof."""
from itertools import combinations,product

units=((1,0),(0,1),(-1,0),(0,-1))
def mul(x,y):return x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def sub(x,y):return x[0]-y[0],x[1]-y[1]
for g,a,b in product(units,repeat=3):
    c=mul(sub(g,a),b)
    if c!=(0,0):assert not c[0] or not c[1] or abs(c[0])==abs(c[1])

def check(m):
 n=3*m
 pairs=list(combinations(range(n),2))
 monomials=[sum(((x>>i&1)*(x>>j&1))<<k for k,(i,j) in enumerate(pairs)) for x in range(1<<n)]
 target=[(-1)**sum(((x>>(3*j))&7)==7 for j in range(m)) for x in range(1<<n)]
 count=0
 for a in range(1<<len(pairs)):
    vals=[v*((-1)**((a&bits).bit_count()%2)) for v,bits in zip(target,monomials)]
    for j in range(n):
        for x in range(1<<n):
            k=1<<j
            if not x&k:vals[x],vals[x+k]=vals[x]+vals[x+k],vals[x]-vals[x+k]
    assert all(v%(2<<m)==1<<m for v in vals)
    count+=len(vals)
 return count
assert check(1)==64 and check(2)==2097152
for x in range(64):
 d,e=(x&7)==7,((x>>3)&7)==7
 assert 1-2*d-2*e+4*d*e==(-1)**(d+e)
print('64 one-copy and 2097152 two-copy real Walsh sums, the root-difference check, and all 64 upper-bound values passed')
