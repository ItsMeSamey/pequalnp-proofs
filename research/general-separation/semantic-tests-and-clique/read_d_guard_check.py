"""Tiny raw signed minterm guards with an arbitrary binary-gate suffix."""
from fractions import Fraction
from random import Random
from math import comb


def build(q,guards,hot):
    # q controls, one private data bit, then gates (table, left, right).
    g=[]
    def add(t,a,b):
        g.append((t,a,b))
        return q+len(g)
    acts=[]
    for lits in guards:
        wires=[v if b else add(3,v,v) for v,b in lits]
        root=wires[0]
        for v in wires[1:]:root=add(8,root,v)
        acts.append(root)
    root=acts[0]
    for v in acts[1:]:root=add(8 if hot else 6,root,v)
    add(8,root,q)
    return g,acts


def run(q,guards,hot=False):
    m=len(guards); L=len(guards[0])
    assert all(len(g)==L and len({v for v,b in g})==L for g in guards)
    d=max(sum(any(v==i for v,b in g) for g in guards) for i in range(q))
    p=Fraction(1,2**L)
    hist=[0]*(m+1)
    g,signals=build(q,guards,hot)
    direct=low=high=0
    cut=m//2
    for x in range(1<<q):
        expected=[int(all(x>>j&1==b for j,b in guard)) for guard in guards]
        h=sum(expected)
        hist[h]+=1
        for bit in (0,1):
            wires=[x>>j&1 for j in range(q)]+[bit]
            for t,a,b in g:wires.append(t>>(2*wires[a]+wires[b])&1)
            assert [wires[i] for i in signals]==expected
            direct+=wires[-1]
        # Condition on the controls; the residual suffix is either constant
        # zero or the single free data bit, which has one satisfying assignment.
        ways=int(all(expected)) if hot else h%2
        if h>cut:high+=ways
        else:low+=ways
    assert direct==low+high
    for z in (2,3,4):
        lhs=Fraction(sum(n*z**i for i,n in enumerate(hist)),1<<q)
        rhs=(1-p+p*z**d)**m
        assert lhs**d<=rhs
        for k in range(m+1):
            tail=Fraction(sum(hist[k:]),1<<q)
            assert (tail*z**k)**d<=rhs
    return d,hist,low,high


if __name__=='__main__':
    overlapping=[[(0,1),(1,0)],[(1,0),(2,1)],[(2,0),(3,1)],[(3,1),(0,0)]]
    print('signed ring',run(4,overlapping))
    rng=Random(1917)
    for _ in range(40):
        q=rng.randrange(4,9);L=rng.randrange(1,4)
        guards=[[(v,rng.randrange(2)) for v in rng.sample(range(q),L)] for j in range(rng.randrange(2,8))]
        run(q,guards)
    guards=[[(0,1),(1,1)]]*6
    d,h,low,high=run(2,guards,True)
    assert (d,h[-1],low,high)==(6,1,0,1)
    actual=Fraction(h[-1],4)
    # At z=4 even the unoptimized d=1 Chernoff bound is false.
    naive=(Fraction(3,4)+Fraction(4,4))**6/4**6
    assert actual>naive
    print('duplicate guards: actual all-active tail',actual,'false d=1 bound',naive,'low/high witnesses',low,high)
