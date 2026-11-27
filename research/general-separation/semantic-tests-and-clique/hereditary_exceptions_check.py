"""Enumerate hereditary exception classes and exact transversal numbers."""
from math import comb

def exceptions(a,m):
    if not a or m==0:
        return 0
    half=1<<(m-1)
    full=(1<<half)-1
    l,r=a&full,a>>half
    if l and r:
        return max(exceptions(l,m-1),exceptions(r,m-1))
    child=l|r
    return int(child!=full)+exceptions(child,m-1)

def solve(m):
    n=1<<m
    full=(1<<n)-1
    # Minimum exception count among all nonempty subsets of each mask.
    best=bytearray([255])+bytearray(exceptions(a,m) for a in range(1,full+1))
    for i in range(n):
        half=1<<i
        for lo in range(0,full+1,2*half):
            for j in range(lo,lo+half):
                best[j+half]=min(best[j],best[j+half])
    out=[]
    for k in range(m+1):
        wanted=sum(comb(m,j) for j in range(min(k+1,m)+1))
        ball=sum(1<<x for x in range(n) if x.bit_count()<=k+1)
        assert best[full^ball]>k
        exact=n-max(a.bit_count() for a,v in enumerate(best) if v>k)
        assert exact==wanted
        out.append(exact)
    return out

for m in range(5):
    print(m,solve(m))
for n in range(4):
    width=1<<n
    for phi in range(1<<width):
        a=sum(1<<(2*u+b) for u in range(width) for b in range(2)
              if not (b and phi>>u&1))
        assert exceptions(a,n+1)==0 and a.bit_count()==2*width-phi.bit_count()
print('All Boolean tables on at most 3 bits passed the count reduction')
