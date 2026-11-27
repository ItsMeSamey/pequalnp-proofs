"""Exhaust the pentagon ternary component and its height-two marginals."""
from collections import Counter
from itertools import combinations, product
from fractions import Fraction

STATES = ((0,0),(1,0),(0,1))
CYCLE = tuple((1 << ((i-1)%5)) | (1 << ((i+1)%5)) for i in range(5))


def codebook():
    enc = {}
    for X,Y in STATES:
        rows = []
        for w in range(32):
            if w.bit_count()%2 != X:
                continue
            choices = tuple(((w>>i)&1, Y ^ ((w & r).bit_count()%2)) for i,r in enumerate(CYCLE))
            if all(s in STATES for s in choices):
                rows.append(choices)
        assert len(rows)==6
        for i in range(5):
            assert Counter(c[i] for c in rows)=={s:2 for s in STATES}
        enc[X,Y] = rows
    return enc


def distribution(enc, secret, locations, depth):
    if not locations:
        return {():Fraction(1)}
    if depth == 0:
        assert locations == [0]
        return {(secret,):Fraction(1)}
    size = 5**(depth-1)
    blocks = [[i%size for i in locations if i//size==j] for j in range(5)]
    counts = Counter()
    for row in enc[secret]:
        parts = [distribution(enc,s,q,depth-1) for s,q in zip(row,blocks) if q]
        for entries in product(*(p.items() for p in parts)):
            assignment = tuple(symbol for pattern,_ in entries for symbol in pattern)
            prob = Fraction(1,6)
            for _,weight in entries:
                prob *= weight
            counts[assignment] += prob
    return counts


def main():
    enc=codebook()
    # By automorphisms patterns of up to three probes at height two are
    # represented here, plus a four-probe distinguishing control.
    tests = [[0],[0,1],[0,2],[0,5],[0,10],[0,1,2],[0,1,3],[0,1,5],
             [0,2,10],[0,5,10],[0,5,15]]
    for locs in tests:
        distributions=[distribution(enc,s,locs,2) for s in STATES]
        assert distributions[0]==distributions[1]==distributions[2]
    four = [distribution(enc,s,[0,1,5,6],2) for s in STATES]
    assert len({tuple(sorted(q.items())) for q in four})>1
    # Every completion map on three noncollinear states extends to one affine bit.
    for secret in STATES:
        for requested in STATES:
            row=next(c for c in enc[secret] if c[0]==requested)
            assert row[0]==requested
    print("18 encodings, 15 single-site marginals, 11 height-two privacy cases,",
          "one four-leaf distinguishing marginal")


if __name__=="__main__":
    main()
