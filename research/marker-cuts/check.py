from random import Random
from solve import par,solve,symmetric_maps

def brute(A, labels):
    out={}
    for x in range(1<<len(A)):
        if any((x>>i&1) and par(x&r) for i,r in enumerate(A)):
            continue
        p=0
        for i,v in enumerate(labels):
            if x>>i&1:p^=v
        out[p]=x
    return out

rng=Random(4621)
for case in range(1000):
    t=rng.randrange(1,4)
    n=rng.randrange(1,10)
    label=[rng.randrange(1<<t) for _ in range(n)]
    matrices=list(symmetric_maps(t))
    A=[rng.randrange(2)<<i for i in range(n)]
    parts=[[i] for i in range(n)]
    while len(parts)>1:
        u=parts.pop(rng.randrange(len(parts)))
        v=parts.pop(rng.randrange(len(parts)))
        K=rng.choice(matrices)
        for i in u:
            for j in v:
                if par(label[i]&K[label[j]]):
                    A[i]|=1<<j
                    A[j]|=1<<i
        parts.append(u+v)
    out=solve(A,label,t)
    assert out.keys()==brute(A,label).keys()
    for p,x in out.items():
        assert all(not (x>>i&1) or not par(x&r) for i,r in enumerate(A))
        val=0
        for i,w in enumerate(label):
            if x>>i&1:val^=w
        assert val==p
print('1,000 generated decomposable instances passed.')
