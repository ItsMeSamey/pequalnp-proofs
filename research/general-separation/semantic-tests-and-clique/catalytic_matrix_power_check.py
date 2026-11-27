"""GF(2) Berkowitz, rank-one numerator and scalar powers, using independent oracles."""
from itertools import permutations
from random import Random

def apply(a,x):
    return sum(((row&x).bit_count()%2)<<i for i,row in enumerate(a))

def berk(a):
    w=len(a)
    if not w:return 1
    sub=[r>>1 for r in a[1:]]
    r=a[0]>>1
    v=sum((row&1)<<i for i,row in enumerate(a[1:]))
    toe=[1,a[0]&1]
    for _ in range(w-1):
        toe.append((r&v).bit_count()%2)
        v=apply(sub,v)
    q=berk(sub)
    result=0
    for i,entry in enumerate(toe):
        if entry:result ^= q<<i
    return result&((1<<(w+1))-1)

def leibniz(a):
    det=0
    for perm in permutations(range(len(a))):
        term=1
        for i,j in enumerate(perm):
            term=(term if i==j else 0) ^ ((term<<1) if a[i]>>j&1 else 0)
        det^=term
    return det

def power(a,v,t):
    while t:
        if t&1:v=apply(a,v)
        a=[sum(1<<j for j in range(len(a)) if apply(a,apply(a,1<<j))>>i&1)
           for i in range(len(a))]
        t>>=1
    return v

def coeff(p,q,t,w):
    while t:
        prod=0
        for i in range(w):
            if p>>i&1:prod ^=q<<i
        p=sum(((prod>>(2*i+(t&1)))&1)<<i for i in range(w))
        t>>=1
    return p&1

rng=Random(762)
cases=0
for w in range(1,7):
    for _ in range(12):
        m=[rng.getrandbits(w) for j in range(w)]
        q=berk(m)
        assert q==leibniz(m)
        for a,b in [(0,0),(0,1),(1,0),(rng.getrandbits(w),rng.getrandbits(w))]:
            pert=[row^(b if a>>i&1 else 0) for i,row in enumerate(m)]
            q2=berk(pert)
            assert q2==leibniz(pert) and (q^q2)&1==0
            p=(q^q2)>>1
            for t in [0,1,7,rng.getrandbits(87)|(1<<100)]:
                assert coeff(p,q,t,w)==(b&power(m,a,t)).bit_count()%2
                cases+=1
print(cases,'Berkowitz/Leibniz numerator and scalar-power comparisons passed')
