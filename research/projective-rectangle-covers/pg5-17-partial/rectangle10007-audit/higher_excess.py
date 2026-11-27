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
    out.append(Counter(h))
print(E,levels)
for h in out[:40]:print(sorted(h.items()))
