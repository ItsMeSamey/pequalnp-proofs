from random import Random
from itertools import combinations
from gim_binary_parity import solve,profile,prescribed,bits
from quadratic_centroid import independent

rng=Random(2918)
def matrix(n,loopy):
    rows=[0]*n
    for i in range(n):
        for j in range(i+int(loopy)):
            if rng.randrange(2):
                rows[i]|=1<<j
                rows[j]|=1<<i
    return rows
def nonsing(rows,s):
    return len(independent(rows[i]&s for i in bits(s)))==s.bit_count()
counts=[0,0]
for n in (2,4,6,8,10,12,16):
    for _ in range(250):
        rows=matrix(n,False)
        twist=rng.randrange(1<<n)
        ans=solve(rows,twist)
        ok=any(nonsing(rows,twist^sum(((s>>i)&1)*3<<(2*i) for i in range(n//2)))
               for s in range(1<<(n//2)))
        assert (ans is not None)==ok,(rows,twist,ans,ok)
        counts[0]+=1
for n in range(1,10):
    for _ in range(80):
        W=matrix(n,True)
        labels=[rng.randrange(5) for _ in range(n)]
        odd={v for v in set(labels) if rng.randrange(2)}
        ans=profile(W,labels,odd)
        supports=[s for s in range(1<<n) if nonsing(W,s)]
        ok=any({v for v in set(labels) if sum(labels[i]==v for i in bits(s))%2}==odd for s in supports)
        assert (ans is not None)==ok
        target=rng.randrange(8)
        ans=prescribed(W,labels,target)
        def syn(s):
            v=0
            for i in bits(s):
                v^=labels[i]
            return v
        assert (ans is not None)==any(syn(s)==target for s in supports)
        counts[1]+=1
print(counts,'delta-parity and looped profile/syndrome tests passed')

from gim_binary_parity import diagonal_completion
for n in range(1,9):
    for _ in range(40):
        D=matrix(n,True)
        labels=[rng.randrange(8) for j in range(n)]
        target=rng.randrange(8)
        def valid(t):
            s=0
            for i in bits(t):
                s^=labels[i]
            return s==target and len(independent(row^(t&(1<<i)) for i,row in enumerate(D)))==n
        t=diagonal_completion(D,labels,target)
        assert (t is not None)==any(valid(x) for x in range(1<<n))
        assert t is None or valid(t)
print('320 symmetric diagonal completion controls passed')
