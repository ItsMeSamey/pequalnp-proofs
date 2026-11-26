"""Finite-field checks of root counting, diagonal coverage and determinant budgets."""
from fractions import Fraction
from itertools import product
from math import comb
from random import Random


def rank(matrix, p):
    basis = {}
    for source in matrix:
        row = [x % p for x in source]
        for pos in sorted(basis):
            if row[pos]:
                val = row[pos]
                row = [(a-val*b) % p for a,b in zip(row,basis[pos])]
        pos = next((i for i,v in enumerate(row) if v), None)
        if pos is not None:
            inv = pow(row[pos], -1, p)
            basis[pos] = [x*inv % p for x in row]
    return len(basis)


def check(index, n=6, groups=3, nodes=3, p=5):
    rng = Random(index)
    degree = index % 3
    local = [[rng.randrange(groups) for _ in range(n)] for _ in range(nodes)]
    target = [[rng.randrange(groups) for _ in range(n)] for _ in range(nodes)]
    poly = [[[int(i==j)] + [rng.choice([0,0,1,2,3,4]) for _ in range(degree)]
             for j in range(n)] for i in range(n)]
    values, counts, covered = [], [], []
    for t in range(nodes):
        B = [[sum(a * pow(t+1, k, p) for k,a in enumerate(f)) % p for f in row] for row in poly]
        values.append(B)
        ranks = []
        for g in range(groups):
            cols = [j for j in range(n) if local[t][j] == g]
            off = [[B[i][j] for j in cols] for i in range(n) if target[t][i] != g]
            ranks.append(rank(off,p))
        counts.append(sum(ranks))
        covered.append(sum(bool(ranks[g]) for g in local[t]))
    h = [sum(a[i]!=d[i] for a,d in zip(local,target)) for i in range(n)]
    assert sum(h) <= n*degree + sum(covered)
    expected = sum(Fraction(sum(comb(2*k,j)*max(j-k-degree,0) for j in range(2*k+1)), 4**k) for k in h)
    assert expected <= sum(counts)
    for mask in range(1 << n):
        vs = [j for j in range(n) if mask >> j & 1]
        total = sum(len(vs)-rank([[B[i][j] for j in vs] for i in vs],p) for B in values)
        assert total <= degree*len(vs)
    for bits in product((0,1),repeat=groups*nodes):
        selected = [sum(bits[t*groups+target[t][i]]-bits[t*groups+local[t][i]]
                        for t in range(nodes)) for i in range(n)]
        assert sum(max(z-degree,0) for z in selected) <= sum(counts)


if __name__ == '__main__':
    for i in range(48):
        check(i)
    print('48 finite-field layouts, 3072 principal selections, 24576 group colorings passed')
