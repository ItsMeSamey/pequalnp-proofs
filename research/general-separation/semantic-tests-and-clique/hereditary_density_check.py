"""Enumerate all depth-four tries with exact-rational conditional density tests."""
from fractions import Fraction as F
from itertools import combinations

def prune(mask,m,d):
    for level in range(m-1,-1,-1):
        width=1<<(m-level)
        for lo in range(0,1<<m,width):
            block=((1<<width)-1)<<lo
            if (mask&block).bit_count()*d.denominator < width*d.numerator:
                mask &= ~block
    return mask

def smallest_hit(family, m):
    n=1<<m
    # subset transform marks those complements containing a nonempty admissible set
    subs=bytearray(1<<n)
    for a in family:
        subs[a]=1
    for j in range(n):
        half=1<<j
        for lo in range(0,len(subs),2*half):
            for i in range(lo,lo+half):
                subs[i+half] |= subs[i]
    return n-max(i.bit_count() for i,v in enumerate(subs) if not v)

for m in range(5):
    n=1<<m
    allbits=(1<<n)-1
    vals=[]
    for d in (F(1,4),F(1,3),F(3,8),F(1,2),F(2,3)):
        family=[]
        for a in range(1,allbits+1):
            p=prune(a,m,d)
            if p==a:
                family.append(a)
            if (allbits^a).bit_count() < (2*(1-d))**m:
                assert p!=0
        h=smallest_hit(family,m)
        if d<F(1,2):
            assert h>=(2*(1-d))**m
        elif d==F(1,2):
            candidate=sum(1<<x for x in range(n) if x.bit_count()<=1)
            assert h==m+1 and all(candidate&a for a in family)
        else:
            assert family==[allbits]
        vals.append(h)
    print(m,vals)
