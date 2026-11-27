"""Integral Boolean-cube coefficients of native digraph predicates and arithmetic factors."""
from itertools import permutations
from math import prod
from collections import Counter


def values(n, x):
    def edge(i,j):
        return (x >> (n*i+j)) & 1
    rows = [sum(edge(i,j) for j in range(n)) for i in range(n)]
    cols = [sum(edge(i,j) for i in range(n)) for j in range(n)]
    perms = [p for p in permutations(range(n)) if all(edge(i,j) for i,j in enumerate(p))]
    def istour(p):
        seen = {0}
        v = p[0]
        while v not in seen:
            seen.add(v)
            v = p[v]
        return len(seen)==n
    hc = sum(istour(p) for p in perms)
    def reachable(i):
        seen = {i}
        for _ in range(n-1):
            seen |= {j for v in seen for j in range(n) if edge(v,j)}
        return len(seen)==n
    det = 0
    for p in permutations(range(1,n)):
        sign = (-1)**sum(a>b for k,a in enumerate(p) for b in p[k+1:])
        det += sign*prod((rows[i] if i==j else 0) - edge(i,j) for i,j in enumerate(p,1))
    a, b, r = prod(cols), rows[0]*det, prod(rows)
    return (int(all(rows+cols)),int(bool(perms)),int(all(map(reachable,range(n)))),
            a,b,r,a*b,a*r,len(perms),hc)


def transform(column, modulus):
    a = list(column)
    bit = 1
    while bit < len(a):
        for s in range(len(a)):
            if s & bit:
                a[s] -= a[s^bit]
                if modulus:
                    a[s] %= modulus
        bit *= 2
    return a


def run(n):
    data = [values(n,x) for x in range(1<<(n*n))]
    for modulus in (0,2,3):
        c = [transform(col,modulus) for col in zip(*data)]
        for x,row in enumerate(data):
            if x.bit_count() <= n:
                assert c[0][x] == c[1][x] == c[7][x] == row[8]
                assert c[2][x] == c[6][x] == row[9]
            if x.bit_count()!=n:
                assert c[3][x] == c[4][x] == c[5][x] == 0
        if n==2 and not modulus:
            for factor, folded in ((4,6),(5,7)):
                raw, reduced = Counter(), Counter()
                for s,a in enumerate(c[3]):
                    for t,b in enumerate(c[factor]):
                        if a*b:
                            key = tuple((s>>i&1)+(t>>i&1) for i in range(4))
                            raw[key] += a*b
                            reduced[s|t] += a*b
                assert all(sum(key)==4 for key,val in raw.items() if val)
                assert any(max(key)==2 and val for key,val in raw.items())
                assert all(reduced[s]==v for s,v in enumerate(c[folded]))
                assert reduced[6]==1
    if n==3:
        for x in (1|32|128,4|16|64):
            assert data[x][4]==0 and data[x][8:]==(1,0)
        assert any(row[0] and not row[1] for row in data)
        assert any(row[6]>1 for row in data)


if __name__ == '__main__':
    for order in (2,3):
        run(order)
    print('528 matrices, integer/F2/F3 coefficients and both raw products passed.')
