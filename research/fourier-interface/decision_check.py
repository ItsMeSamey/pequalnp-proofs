"""Check modular measurement aliasing and high-order Hermite data over F5."""
from itertools import product
from math import comb
from random import Random

rng = Random(340)
p = 5


def rank(rows, p):
    basis = {}
    for a in rows:
        a = [v % p for v in a]
        for i in sorted(basis):
            if a[i]:
                c = a[i]
                a = [(v-c*w) % p for v,w in zip(a,basis[i])]
        if any(a):
            i = next(i for i,x in enumerate(a) if x)
            fac = pow(a[i], -1, p)
            basis[i] = [(fac*v) % p for v in a]
    return len(basis)


# Confluent Vandermonde with J=9>5 for three nonzero nodes.
for J in (2, 5, 9, 12):
    nodes = [1, 2, 3]
    size = J*len(nodes)
    matrix = [[comb(i,k)*pow(t,i-k,p)%p if i >= k else 0
               for i in range(size)] for t in nodes for k in range(J)]
    assert rank(matrix,p) == size

for _ in range(100):
    n = 8
    w = [rng.randrange(p) for _ in range(n)]
    off = [rng.randrange(-20,21) for _ in range(n//2)]
    # Sum a product of two factors. The first depends on other-group bits only
    # via a rational-rank-one linear form; the second is wholly local.
    left = list(product((0,1),repeat=n//2))
    right = left
    def val(x, y):
        return (1 + x[0]*x[2] + sum(c*b for c,b in zip(off,y))) % p
    def weight(z, v):
        a = 1
        for bit,c in zip(z,v):
            if bit:
                a = a*c % p
        return a
    def local(y):
        return (1+y[0]*y[3]) * weight(y,w[n//2:])
    direct = sum(val(x,y)*weight(x,w[:n//2])*local(y) for x in left for y in right) % p
    grouped = 0
    for q in range(p):
        ys = [y for y in right if sum(c*b for c,b in zip(off,y)) % p == q]
        if ys:
            grouped += sum(val(x,ys[0])*weight(x,w[:n//2]) for x in left)*sum(local(y) for y in ys)
    assert direct == grouped % p
print("4 high-order Hermite ranks and 100 modular measurement contractions passed")
