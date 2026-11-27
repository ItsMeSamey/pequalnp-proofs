"""Exhaustive projective blocker checks in dimensions three and four."""
from itertools import combinations, permutations, product
from collections import Counter


def normalize(p):
    scale = next((x for x in p if x), 0)
    return tuple(x * scale % 3 for x in p)


def projective(d):
    return [p for p in product(range(3), repeat=d) if any(p) and p == normalize(p)]


def vanishing_masks(points):
    return [sum(1 << i for i, q in enumerate(points)
                if sum(x*y for x, y in zip(p, q)) % 3 == 0) for p in points]


def minimal(masks, full):
    seen = 0
    repeated = 0
    for mask in masks:
        repeated |= seen & mask
        seen |= mask
    return seen == full and all(m & ~repeated for m in masks)


def rank_three():
    points = projective(3)
    masks = vanishing_masks(points)
    full = (1 << len(points)) - 1
    minimal_sets = set()
    for k in range(1, 14):
        for ids in combinations(range(13), k):
            if minimal([masks[i] for i in ids], full):
                minimal_sets.add(frozenset(points[i] for i in ids))
    graphic = set()
    for a,b,c in permutations((p for p in product(range(3),repeat=3) if any(p)),3):
        det = sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3]) for i in range(3))
        if det % 3:
            edges = [a,b,c] + [tuple((x-y)%3 for x,y in zip(p,q)) for p,q in ((a,b),(b,c),(a,c))]
            graphic.add(frozenset(map(normalize,edges)))
    assert graphic == {s for s in minimal_sets if len(s)==6}
    assert Counter(map(len,minimal_sets)) == {4:13,6:234}


def rank_four():
    points = projective(4)
    masks = dict(zip(points,vanishing_masks(points)))
    basis = [p for p in points if sum(bool(x) for x in p)==1]
    extra = [p for p in points if p not in basis]
    full = (1 << len(points)) - 1
    for k, expected in enumerate((0,0,0,72)):
        found = sum(minimal([masks[p] for p in (*basis,*sub)],full)
                    for sub in combinations(extra,k))
        assert found == expected
    example = basis + [(1,1,0,0),(0,0,1,1),(1,2,1,2)]
    assert minimal([masks[p] for p in example],full)


if __name__=="__main__":
    rank_three()
    rank_four()
    print("PG(2,3): 13 pencils, 234 K4 copies. Rank four: minimum 7, 72 extensions of fixed basis.")
