"""Verify coset-batched Walsh convolution with exact integers."""
from collections import defaultdict
from random import Random
from check import span


def hadamard(v):
    a = list(v)
    stride = 1
    while stride < len(a):
        for i in range(0, len(a), 2*stride):
            for k in range(i, i+stride):
                x, y = a[k], a[k+stride]
                a[k], a[k+stride] = x+y, x-y
        stride *= 2
    return a


def check(A, B, E, rng):
    total = lambda X,Y: {x^y for x in X for y in Y}
    P, L, R = total(A,B)&E, A&total(B,E), B&total(A,E)
    K, J = A&B, A&B&E
    # Numeric order on a binary subspace gives a linear indexing of J.
    js = sorted(J)
    assert all(js[i^h] == x^y for i,x in enumerate(js) for h,y in enumerate(js))
    rep = lambda a: min(a^j for j in J)
    f, g = {x:rng.randrange(-4,5) for x in L}, {x:rng.randrange(-4,5) for x in R}
    direct = {s:sum(v*g.get(s^a,0) for a,v in f.items()) for s in P}
    output = defaultdict(int)
    pairs = {(rep(x),rep(y)) for x in L for y in R if x^y in P}
    assert len(pairs)*len(J)**2 == len(P)*len(K)
    for a,b in pairs:
        left = hadamard([f[a^j] for j in js])
        right = hadamard([g[b^j] for j in js])
        cv = hadamard([x*y for x,y in zip(left,right)])
        for j,v in zip(js,cv):
            assert v % len(js) == 0
            output[a^b^j] += v//len(js)
    assert direct == output
    assert (len(P)*len(K)//len(J))**2 <= len(P)*len(L)*len(R)


rng = Random(221)
for _ in range(300):
    d = rng.randrange(2, 7)
    check(*(span([rng.randrange(1<<d) for _ in range(rng.randrange(1,d+2))]) for _ in range(3)), rng)
print("300 coset-batched Walsh forks matched direct convolution")
