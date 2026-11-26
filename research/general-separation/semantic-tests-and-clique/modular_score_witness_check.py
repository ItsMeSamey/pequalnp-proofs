"""Expand 1-S^(p-1), retain prefix row representatives, and check true witnesses."""
from itertools import product
from random import Random

def mult(a,b,p):
    out={}
    for (u,v),c in a.items():
        for (x,y),d in b.items():
            if (u|x)&(v|y):
                continue
            key=(u|x,v|y)
            out[key]=(out.get(key,0)+c*d)%p
    return {k:v for k,v in out.items() if v}

def test(n,clauses,p):
    s={}
    for k in clauses:
        s[k]=(s.get(k,0)+1)%p
    power={(0,0):1}
    for _ in range(p-1):
        power=mult(power,s,p)
    q={k:-v%p for k,v in power.items()}
    q[0,0]=(q.get((0,0),0)+1)%p
    terms=[(u,v,c) for (u,v),c in q.items() if c]
    def row(x,k):
        m=(1<<k)-1
        return [int((u&m)&~x==0 and (v&m)&x==0) for u,v,_ in terms]
    reps=[0]
    for k in range(1,n+1):
        pivots={}
        keep=[]
        for x0 in reps:
            for x in (x0,x0|(1<<(k-1))):
                r=row(x,k)
                for i,y in sorted(pivots.items()):
                    c=r[i]
                    r=[(a-c*b)%p for a,b in zip(r,y)]
                if any(r):
                    pivot=next(i for i,c in enumerate(r) if c)
                    scale=pow(r[pivot],-1,p)
                    pivots[pivot]=[a*scale%p for a in r]
                    keep.append(x)
        reps=keep
    def violations(x):
        return sum((u&~x)==0 and (v&x)==0 for u,v in clauses)
    def value(x):
        return sum(c*b for (_,_,c),b in zip(terms,row(x,n)))%p
    raw=list(range(1<<n))
    assert all(value(x)==int(violations(x)%p==0) for x in raw)
    hits=[x for x in reps if value(x)]
    assert bool(hits)==any(value(x) for x in raw)
    if all(violations(x)%p or violations(x)==0 for x in raw):
        assert bool(hits)==any(violations(x)==0 for x in raw)
        assert all(all((u&~x) or (v&x) for u,v in clauses) for x in hits)
    return hits

rng=Random(733)
for p in (2,3,5):
    for _ in range(80):
        n=4
        cs=[]
        for i in range(rng.randrange(8)):
            a=rng.randrange(1<<n)
            cs.append((a,rng.randrange(1<<n)&~a))
        test(n,cs,p)
    assert test(1,[(0,0)]*p,p) # infeasible formula, score always p.
print('240 random and 3 bad-multiple controls passed')
