from fractions import Fraction as F
from collections import Counter
import sys
E=int(sys.argv[1]) if len(sys.argv)>1 else 73
s,b=F(17125,93899),F(3030,93899)
budget=E*s+31*b-14
def parts(n,largest):
    if not n:
        yield ()
    for j in range(1,min(n,largest)+1):
        for t in parts(n-j,j):
            yield (j,)+t
def cost(t):
    e=sum(t)
    return F((25+e)**2,125*(25+2*e+sum(v*v for v in t))-4*(25+e)**2)-1+s*e+b
types=[]
for e in range(E+1):
    if cost((e,))>budget:continue
    for t in parts(e,e):
        if cost(t)<=budget and t not in ((2,),(3,)):
            types.append((t,cost(t)))
def visit(pos,k,e,gaps,h):
    if pos==len(types):
        c3=e-2*k
        c2=k-c3
        if min(c3,c2)<0:return
        hh=h+[(2,)]*c2+[(3,)]*c3
        yield hh
        return
    t,c=types[pos]
    for a in range(k+1):
        if a*sum(t)>e or c*a>gaps:return
        yield from visit(pos+1,k-a,e-a*sum(t),gaps-a*c,h+[t]*a)
levels=Counter()
out=[]
for h in visit(0,31,E,budget,[]):
    levels['raw']+=1
    r2=sum(any(x%2 for x in t) for t in h)
    if r2<14:continue
    one2=sum(sum(x%2 for x in t)==1 for t in h)
    if one2>3*2**(r2-14):continue
    # Every repeated pure row class (2 or 3 copies) has <=3 zeros total.
    # All pure rows are nonzero with weight >=r2-7; repeated ones >=r2-3.
    d2=r2-14
    poss=False
    for singles in range(one2+1):
        for doubles in range((one2-singles)//2+1):
            rem=one2-singles-2*doubles
            if rem%3: continue
            triples=rem//3
            repeat=doubles+triples
            if (repeat>d2 and 3*repeat<r2) or repeat>d2+1 or singles+repeat>2**d2-1: continue
            if 3*repeat<r2 and repeat:
                # Restricted rows outside the union of the <=3 supports of 1+B_C.
                outside=r2-3*repeat
                possible_patterns=2**(d2-repeat+1)-1-int(outside>7)
                if one2>3*repeat+3*possible_patterns:continue
            if singles*(r2-7)+repeat*(r2-3)> (2**(d2-1) if d2 else 0)*r2: continue
            poss=True
    if not poss:continue
    levels['mod2']+=1
    r3=sum(any(x%3 for x in t) for t in h)
    if r3<14:continue
    levels['mod3']+=1
    pure2=sum([x%3 for x in t if x%3]==[2] for t in h)
    if pure2>(3**(r3-14)-1)//2:continue
    levels['rays']+=1
    m=pure2
    if m-int(m%3==1)>(r3-14)*(r3-13)//2: continue
    levels['square']+=1
    pure1=sum([x%3 for x in t if x%3]==[1] for t in h)
    if pure1 and pure2+1>(r3-14)*(r3-13)//2: continue
    levels['ones']+=1
    out.append(Counter(h))
print(E,levels)
for h in out[:40]:print(sorted(h.items()))
if E==75:
    assert len(out)==2
    for h in out:
        assert all(len(row)<=1 for row in h)
        pairs=sum(n*sum(x*(x+1)//2 for x in row) for row,n in h.items())
        assert pairs>136
        print('intersection pairs required',pairs)
