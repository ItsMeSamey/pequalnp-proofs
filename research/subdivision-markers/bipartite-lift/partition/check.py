from itertools import combinations
from random import Random
from recognize import recognize


def rank(rows,mask):
    basis = {}
    for i,row in enumerate(rows):
        if not ((mask>>i)&1):
            continue
        v = row & mask
        while v:
            p = v.bit_length()-1
            if p not in basis:
                basis[p] = v
                break
            v ^= basis[p]
    return len(basis)


def oracle(rows):
    n = len(rows)
    full = (1<<n)-1
    return min(rank(rows,m)+rank(rows,full^m) for m in range(1<<n))


def audit(rows):
    n = len(rows)
    optimum = oracle(rows)
    for k in (-1,0,1,2,3,4,5,n):
        ans = recognize(rows,k)
        assert (ans is not None) == (optimum<=k)
        if ans is not None:
            colors,left,right = ans
            assert all(colors[v]==s for s,base in enumerate((left,right)) for v in base)
            masks = [sum(1<<v for v,c in enumerate(colors) if c==s) for s in (0,1)]
            assert [rank(rows,m) for m in masks] == [len(left),len(right)]
            assert len(left)+len(right) == optimum
    return optimum


if __name__ == '__main__':
    from collections import Counter
    tally = Counter()
    for n in range(6):
        edges = list(combinations(range(n),2))
        for graph in range(1 << len(edges)):
            rows = [0]*n
            for j,(u,v) in enumerate(edges):
                if (graph>>j)&1:
                    rows[u] |= 1<<v
                    rows[v] |= 1<<u
            tally[audit(rows)] += 1
    rng = Random(64954)
    for i in range(120):
        n = rng.randrange(6,11)
        rows = [0]*n
        for u,v in combinations(range(n),2):
            if rng.random() < (i%9+1)/10:
                rows[u] |= 1<<v
                rows[v] |= 1<<u
        tally[audit(rows)] += 1
    # Cliques of odd order have optimum n-1, exercising larger budgets.
    for n in (7,9):
        tally[audit([((1<<n)-1)^(1<<i) for i in range(n)])] += 1
    print('graphs by optimum',dict(sorted(tally.items())))
