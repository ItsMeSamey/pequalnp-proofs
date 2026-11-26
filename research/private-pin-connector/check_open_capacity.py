"""Test arbitrary separate decoders via components of the accepted port relation."""
from random import Random
from math import isqrt
rng=Random(701)
def rank(vectors):
    basis={}
    for v in vectors:
        while v:
            k=v.bit_length()
            if k not in basis:
                basis[k]=v
                break
            v^=basis[k]
    return len(basis)
def vals(cols):
    out=[0]
    for v in cols:out += [x^v for x in out]
    return out
def test():
    nl,nr,pl,pr=(rng.randrange(1,4) for _ in range(4))
    ell,rr=nl+pl,nr+pr
    rows=[rng.randrange(1<<rr) for _ in range(ell)]
    k=rng.randrange(6)
    a=[rng.randrange(1<<k) for _ in rows]
    b=[rng.randrange(1<<k) for _ in range(rr)]
    vx,vy,neighbors=vals(a),vals(b),vals(rows)
    masks=[(1<<pl)-1,(1<<pr)-1]
    allowed=[set() for _ in range(1<<k)]
    for y in range(1<<rr):
        forbidden=sum(((row&y).bit_count()%2)<<i for i,row in enumerate(rows[:pl]))
        for x in range(1<<ell):
            if x&forbidden or neighbors[x]&y&masks[1]:continue
            allowed[vx[x]^vy[y]].add((x>>pl,y>>pr))
    h=rank(a)+rank(b)
    for E in allowed:
        classes=[]
        for x,y in E:
            new={x,~y}
            touched=[c for c in classes if new&c]
            for c in touched:
                new|=c
                classes.remove(c)
            classes.append(new)
        assert len(classes)**2<=1<<h
    return len(allowed)
print(sum(test() for _ in range(1500)), 'target relations passed for arbitrary separate decoders')
