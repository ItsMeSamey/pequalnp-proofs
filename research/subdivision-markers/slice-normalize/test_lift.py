from itertools import product
from random import Random
from lift import build,products
from solver import parity,quadratic

def valid(M,e,x):
    return all(parity(x&a)==b for a,b in e) and all(not x>>i&1 or not parity(x&r) for i,r in enumerate(M))

def check(M,e):
    n = len(M)
    lift = build(M,e)
    pairs,r = products(M,e)
    assert len(pairs)<=r+1
    for x in range(1<<n):
        if all(parity(x&a)==b for a,b in e):
            assert quadratic(M,x)==sum(parity(x&p)*parity(x&q) for p,q in pairs)%2
    expected = {x for x in range(1<<n) if valid(M,e,x)}
    found = {y&((1<<n)-1) for y in range(1<<len(lift.graph)) if valid(lift.graph,lift.equations,y)}
    assert expected==found
    for x in expected:
        y = lift.repair(x)
        assert y&((1<<n)-1)==x and valid(lift.graph,lift.equations,y)
    return len(expected)

if __name__ == '__main__':
    rng = Random(6621)
    count = hits = 0
    for n in range(4):
        # All matrices and all distinct codimension-zero/one fibers.
        fibers = [[]]+[[(m,b)] for m in range(1,1<<n) for b in (0,1)]
        for M in product(range(1<<n),repeat=n):
            for e in fibers:
                hits += check(M,e)
                count += 1
    for _ in range(100):
        n = rng.randrange(4,6)
        M = [rng.randrange(1<<n) for i in range(n)]
        x = rng.randrange(1<<n)
        e = [(m,parity(m&x)) for m in (rng.randrange(1<<n) for i in range(rng.randrange(4)))]
        hits += check(M,e)
        count += 1
    print(count,'projected witness sets;',hits,'small repaired witnesses',flush=True)
    max_n = max_lift = max_c = 0
    for _ in range(120):
        n = rng.randrange(18,65)
        x = rng.getrandbits(n)
        e = [(m,parity(m&x)) for m in (rng.getrandbits(n) for i in range(rng.randrange(6)))]
        M = [rng.getrandbits(n) for i in range(n)]
        for i,row in enumerate(M):
            if x>>i&1 and parity(row&x):
                M[i] ^= 1<<i
        lift = build(M,e)
        y = lift.repair(x)
        assert valid(lift.graph,lift.equations,y) and y&((1<<n)-1)==x
        max_n,max_lift,max_c = max(max_n,n),max(max_lift,len(lift.graph)),max(max_c,len(lift.factors))
    print('120 planted random witness repairs; maxima', max_n,max_lift,max_c)
