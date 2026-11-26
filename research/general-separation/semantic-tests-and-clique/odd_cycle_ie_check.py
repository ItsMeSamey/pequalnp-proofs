"""Check the affine-event minimum and literal telescoping certificate over Q."""
from fractions import Fraction as F
from itertools import product
from math import comb

def independent(cols,target):
    pivots={}
    def reduce(col):
        r=list(map(F,col))
        for p,v in sorted(pivots.items()):
            d=r[p]
            r=[a-d*b for a,b in zip(r,v)]
        return r
    for col in cols:
        r=reduce(col)
        if any(r):
            p=next(i for i,y in enumerate(r) if y)
            pivots[p]=[y/r[p] for y in r]
    return any(reduce(target))

for n in range(3,9):
    patterns=set()
    literal_rows=[]
    for x in product(range(2),repeat=n):
        literals=[]
        for i in range(n-1):
            literals.extend((x[i]*(1-x[i+1]),(1-x[i])*x[i+1]))
        literals.extend((x[-1]*x[0],(1-x[-1])*(1-x[0])))
        synd=tuple(a+b for a,b in zip(literals[::2],literals[1::2]))
        patterns.add(synd)
        telescope=sum(literals[::2])-sum(literals[1::2])
        assert telescope==2*x[0]-1 and telescope**2==1
        literal_rows.append(literals)
    assert patterns=={y for y in product(range(2),repeat=n) if sum(y)%2}
    weights=sorted({sum(y) for y in patterns})
    for d in range(1,len(weights)+1):
        cols=[[comb(t,j) for t in weights] for j in range(1,d+1)]
        assert independent(cols,[1]*len(weights))==(d<len(weights))
    assert independent(zip(*literal_rows),[1]*len(literal_rows))
    print(n,len(weights),2)
