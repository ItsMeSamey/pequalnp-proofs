from itertools import combinations
from random import Random
rng=Random(31811)
def had(a):
    i=1
    while i<len(a):
        for j in range(0,len(a),2*i):
            for h in range(j,j+i):
                a[h],a[h+i]=a[h]+a[h+i],a[h]-a[h+i]
        i*=2
    return a
def cubic(x,t):
    return sum(((x>>(3*i))&7)==7 for i in range(t))%2
def bases(n,d):
    for piv in combinations(range(n),d):
        slots=[(r,c) for r,p in enumerate(piv) for c in range(p+1,n) if c not in piv]
        for mask in range(1<<len(slots)):
            basis=[1<<p for p in piv]
            for j,(r,c) in enumerate(slots):
                if mask>>j & 1: basis[r]|=1<<c
            yield basis
stats={}
for k in range(7):
    low=1<<20; cases=0
    for bs in bases(6,6-k):
        points=[0]
        for v in bs: points += [v^x for x in points]
        quads=list(combinations(range(len(bs)),2))
        for j in range(5):
            a=rng.randrange(64) if j else 0
            mons=[(1<<i)|(1<<b) for i,b in quads if j and rng.randrange(2)]
            vals=[(-1)**(cubic(v^a,2)+sum((idx&p)==p for p in mons)) for idx,v in enumerate(points)]
            spectrum=had(vals)
            size=(1<<k)*sum(bool(z) for z in spectrum)
            low=min(low,size)
            assert size>=1<<(k+3*max(2-k,0))
            cases+=1
    assert low==1<<(k+3*max(2-k,0))
    stats[k]=(cases,low)
print("All 6-bit subspaces with five basepoint/phase choices; (cases,min) by codimension:",stats)
