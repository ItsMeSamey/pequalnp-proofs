"""Check the two-marker fundamental-graph criterion against direct enumeration."""
from random import Random
from itertools import combinations
def span(cols):
    s={0}
    for a in cols:
        s |= {v^a for v in s}
    return s
def labels(cols,w):
    z=0
    for i,x in enumerate(cols):
        if w>>i&1:
            z^=x
    return z
def test(cols,e,f):
    n=len(cols)
    whole=span(cols+[e,f])
    if not f or span(cols+[f]) != whole:
        return False
    b=[f]
    for i,x in enumerate(cols):
        if x not in span(b):
            b.append(x)
    co={labels(b,w):w for w in range(1<<len(b))}
    if not co[e]&1:
        return True
    # Alternative paths through fundamental graph between basis row f
    # and nonbasis column e, excluding their direct edge.
    reached = 1
    while True:
        nxt=reached
        for x in cols:
            v=co[x]
            if v&reached:
                nxt |= v
        if nxt==reached:
            return bool(co[e]&reached&~1)
        reached=nxt
def run():
    rng=Random(5801)
    for _ in range(2500):
        n=rng.randrange(1,9); r=rng.randrange(1,6)
        cols=[rng.randrange(1<<r) for i in range(n)]
        e,f=[rng.randrange(1<<r) for i in range(2)]
        good=False
        for mask in range(1<<n):
            V=span([x for i,x in enumerate(cols) if mask>>i&1])
            if e in V and f not in V:
                good=True; break
        assert test(cols,e,f)==good,(cols,e,f)
    print("2500 random labelled two-terminal minors agree")
if __name__=='__main__':
    run()
