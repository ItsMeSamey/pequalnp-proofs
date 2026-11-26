"""Finite part of the one-proper-support exclusion. All rank tests use integers."""
from fractions import Fraction
from itertools import combinations_with_replacement, product


def rank(rows):
    basis = {}
    for row in rows:
        row = list(map(Fraction, row))
        for pivot,vec in sorted(basis.items()):
            scale = row[pivot]
            row = [a - scale*b for a,b in zip(row,vec)]
        pivot = next((i for i,a in enumerate(row) if a),None)
        if pivot is not None:
            basis[pivot] = [a/row[pivot] for a in row]
    return len(basis)


def parity(trace, mask):
    return sum((s<0) for i,s in enumerate(trace) if (mask>>i)&1)%2


kept=[]
for weights in combinations_with_replacement((1,3,5),6):
    rows=[(1,)+tail for tail in product((1,-1),repeat=5)]
    dot=lambda s:sum(a*b for a,b in zip(weights,s))
    rows=[row for row in rows if abs(dot(row))==4]
    if rank(rows)<6: continue
    assert len(rows)==6
    outputs=sum((dot(row)<0)<<i for i,row in enumerate(rows))
    affine={sum((parity(row,mask)^b)<<i for i,row in enumerate(rows))
            for mask in range(64) for b in (0,1)}
    assert all((outputs^(1<<i)) in affine for i in range(6))
    kept.append(weights)
assert kept==[(1,1,1,1,1,1),(1,1,1,1,3,3)]
print('28 profiles checked; both independent profiles force six disjoint cubic-plus-quadratic cells')
