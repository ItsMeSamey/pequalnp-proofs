"""Finite controls for pairwise independent support-extension equations."""
from itertools import combinations
from random import Random


def basis_rank(rows):
    basis = {}
    for p in rows:
        while p and p.bit_length() in basis:
            p ^= basis[p.bit_length()]
        if p:
            basis[p.bit_length()] = p
    return len(basis)


def equations(n, prescribed, selected):
    edges = list(combinations(range(n), 2))
    return [sum(1 << j for j,(a,b) in enumerate(edges)
                if (a==i and selected & (1<<b)) or (b==i and selected & (1<<a)))
            for i in range(n) if (prescribed | selected) & (1<<i)]


def pair_check():
    count = 0
    for n in range(4,8):
        p = 3
        for fixed in range(4):
            vals = [d for d in range(1,1<<n) if (d&p)==fixed]
            for d,e in combinations(vals,2):
                l,r=equations(n,p,d),equations(n,p,e)
                assert basis_rank(l)==(p|d).bit_count()-1
                assert basis_rank(l+r)==basis_rank(l)+basis_rank(r)
                count += 1
    return count


def actual_check():
    n = 15
    rng = Random(66291)
    A = [0]*n
    for i,j in combinations(range(n),2):
        if rng.getrandbits(1):
            A[i] |= 1<<j
            A[j] |= 1<<i
    pairs=list(combinations(range(n),2))
    seen={(i,j,X,Y):set() for i,j in pairs for X,Y in ((0,0),(1,0),(0,1))}
    for w in range(1<<n):
        X=w.bit_count()%2
        for Y in ((0,) if X else (0,1)):
            z=tuple(((w>>i)&1) + 2*(Y^((w&a).bit_count()%2)) for i,a in enumerate(A))
            if 3 in z:
                continue
            for i,j in pairs:
                seen[i,j,X,Y].add((z[i],z[j]))
    assert min(map(len,seen.values()))==9
    return sum(map(len,seen.values()))


if __name__=="__main__":
    print(pair_check(),"pairwise-rank controls;",actual_check(),"two-site extensions")
