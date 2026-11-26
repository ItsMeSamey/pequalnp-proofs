"""Signed anchor expansions with arbitrary overlapping anchors and crossing cores."""
from collections import defaultdict
from itertools import product
from random import Random

def subwords(mask):
    s=mask
    while True:
        yield s
        if not s:
            return
        s=(s-1)&mask


def rows(anchor,clauses):
    grouped = defaultdict(list)
    for mask,pins in clauses:
        for t in subwords(anchor&~mask):
            grouped[t|(pins&anchor)].append((mask&~anchor,pins&~anchor))
    sparse = [(1,0,0,[])]
    for a,residual in grouped.items():
        sparse.append((-1,anchor,a,[]))
        if all(m for m,b in residual):
            sparse.append((1,anchor,a,residual))
    dense = [(1,anchor,a,grouped.get(a,[])) for a in subwords(anchor)]
    return min((sparse,dense),key=len)


def verify(n,anchors,clusters,core):
    outputs = [rows(a,c) for a,c in zip(anchors,clusters)]
    evaluations = [0]*(1<<n)
    for selection in product(*outputs):
        mask = pins = 0
        sign = 1
        short = core.copy()
        for s,m,b,r in selection:
            if (b^pins)&m&mask:
                break
            mask |= m
            pins |= b
            sign *= s
            short += r
        else:
            for x in range(1<<n):
                if x&mask==pins and all(x&m!=b for m,b in short):
                    evaluations[x] += sign
    assert evaluations==[int(all(x&m!=b for m,b in core+sum(clusters,[]))) for x in range(1<<n)]


if __name__=='__main__':
    rng = Random(1234)
    for trial in range(600):
        n = rng.randrange(1,7)
        cap = (1<<n)-1
        def family():
            current = []
            for _ in range(rng.randrange(6)):
                m = rng.randrange(cap+1)
                current.append((m,m&rng.randrange(cap+1)))
            return current
        anchors = [rng.randrange(cap+1) for _ in range(rng.randrange(4))]
        verify(n,anchors,[family() for a in anchors],family())
    print('600 signed cluster tests passed pointwise')
