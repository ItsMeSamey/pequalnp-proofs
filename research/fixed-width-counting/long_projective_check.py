"""Finite projective plane nonincidence supports and closure inversion tests."""
from itertools import combinations, product
from math import comb
from collections import Counter
from long_pivot_check import columns


def plane(q):
    labels = [(1,a,b) for a,b in product(range(q),repeat=2)]
    labels += [(0,1,b) for b in range(q)]+[(0,0,1)]
    return [sum(1<<i for i,p in enumerate(labels) if sum(a*b for a,b in zip(p,l))%q)
            for l in labels]


def test_plane(q):
    matrix = plane(q)
    n = q*q+q+1
    assert len(matrix)==n and all(row.bit_count()==q*q for row in matrix)
    assert all((r&s).bit_count()%2==(i==j)
               for i,r in enumerate(matrix) for j,s in enumerate(matrix))
    for four in combinations(range(n),4):
        mask = sum(1<<i for i in four)
        assert not all(any(row&mask==1<<i for row in matrix) for i in four)
    triangular = next(t for t in combinations(range(n),3) if all(
        any(row&sum(1<<j for j in t)==1<<i for row in matrix) for i in t))
    assert triangular
    closure = {0}
    for column in matrix:  # point/line dot-product construction is self-dual
        closure.update([p|column for p in closure])
    small = {0}
    for k in range(1,4):
        for seq in combinations(matrix,k):
            bits = 0
            for s in seq:
                bits |= s
            small.add(bits)
    assert small==closure and len(small)<=sum(comb(n,j) for j in range(4))
    return len(closure)


def test_inversion(n,clauses):
    cols = columns(n,clauses)
    closure = {0}
    for pair in cols:
        for v in pair:
            closure.update([c|v for c in closure])
    def assignment(x):
        out = 0
        for i,(a,b) in enumerate(cols):
            out |= b if x>>i&1 else a
        return out
    for core in (lambda x:True,lambda x:x%3==1):
        direct = Counter(assignment(x) for x in range(2**n) if core(x))
        exact = {}
        for mask in sorted(closure,key=int.bit_count):
            domains = [[b for b in (0,1) if pair[b]&~mask==0] for pair in cols]
            down = sum(core(sum(v<<i for i,v in enumerate(bits))) for bits in product(*domains))
            exact[mask] = down-sum(v for t,v in exact.items() if t&~mask==0)
        assert all(exact[u]==direct[u] for u in closure)


def two_plane_product(q):
    plane_rows = plane(q)
    n = len(plane_rows)
    rows = [a|(b<<n) for a,b in product(plane_rows,repeat=2)]
    columns = [sum(1<<i for i,row in enumerate(rows) if row>>j&1) for j in range(2*n)]
    closure = {0}
    basis = {}
    for c in columns:
        closure.update([v|c for v in closure])
        row = c
        while row and row.bit_length() in basis:
            row ^= basis[row.bit_length()]
        if row:
            basis[row.bit_length()] = row
    assert all(row.bit_count()==2*q*q for row in rows)
    assert len(set(rows))==n*n and len(basis)==2*n-1
    assert len(closure)==(2*n+1)**2+1
    return len(rows),2*q*q,len(basis),len(closure)


if __name__=='__main__':
    for q in (3,5):
        print('q',q,'distinct unions',test_plane(q))
    print('two-plane product (rows,width,rank,profiles)',two_plane_product(3))
    cases = 0
    for n,limit in ((0,1),(1,3),(2,9),(3,3)):
        universe = [(m,b) for m,b in product(range(2**n),repeat=2) if b&m==b]
        for k in range(limit+1):
            for family in combinations(universe,k):
                test_inversion(n,family)
                cases += 1
    print('closure inversion cases:',cases)
