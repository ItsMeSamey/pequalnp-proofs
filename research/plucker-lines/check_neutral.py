from random import Random
from itertools import combinations

def check(rows,P,Q,z):
    n=len(rows)
    witness=None
    for r in range(2):
        for i in P[r]:
            for l in Q[r]:
                if not(rows[i]>>l&1):
                    witness=(1<<i)|(1<<l)
    if witness is None:
        for r in range(2):
            for i in P[r]:
                zero=[j for j in Q[1-r] if not rows[z]>>j&1 and not rows[i]>>j&1]
                one=[k for k in Q[1-r] if rows[z]>>k&1 and rows[i]>>k&1]
                last=[l for l in Q[r] if rows[z]>>l&1]
                if zero and one and last:
                    witness=sum(1<<v for v in (z,i,zero[0],one[0],last[0]))
    def ok(s):
        if sum(s>>i&1 for part in P for i in part)%2==0:return False
        if sum(s>>i&1 for part in Q for i in part)%2==0:return False
        if sum(s>>i&1 for i in P[1]+Q[1])%2:return False
        return all(not(s>>i&1) or not((s&a).bit_count()%2) for i,a in enumerate(rows))
    if witness is not None:assert ok(witness)
    assert (witness is not None)==any(ok(x) for x in range(1<<n))
    return None if witness is None else witness.bit_count()

rng=Random(707)
counts={None:0,2:0,5:0}
for trial in range(1300):
    n=rng.randrange(5,13)
    P=[[0],[1]]
    Q=[[2],[3]]
    z=4
    for i in range(5,n):
        rng.choice(P+Q).append(i)
    rows=[0]*n
    complete=trial%3!=0
    for r in range(2):
        for j in Q[r]:
            for i in [z]+P[0]+P[1]:
                if (complete and i in P[r]) or rng.randrange(2):
                    rows[i]|=1<<j
                    rows[j]|=1<<i
    counts[check(rows,P,Q,z)]+=1
print(counts)
