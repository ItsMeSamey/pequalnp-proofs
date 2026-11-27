from itertools import combinations
from random import Random

from common_neighbor_bags import proposals


def check(n, h, isolated):
    rng = Random(n * 170 + h)
    pairs = list(combinations(range(n), 2))
    labels = [("raw", 31*i+7) for i in range(len(pairs)*h)]
    rng.shuffle(labels)
    bags = dict(zip(pairs, (labels[i:i+h] for i in range(0,len(labels),h))))
    edges = [(a,b) for p,q in combinations(pairs,2) if set(p).isdisjoint(q)
             for i,a in enumerate(bags[p]) for j,b in enumerate(bags[q]) if i!=j]
    vertices = labels + ([("unused", -1)] if isolated else [])
    expected = {frozenset(b) for b in bags.values()}
    if isolated:
        expected.add(frozenset([vertices[-1]]))
    rng.shuffle(vertices)
    rng.shuffle(edges)
    candidates = list(proposals(vertices, edges))
    assert sum({frozenset(b) for b in part}==expected for part in candidates)==1
    for part in candidates:
        assert set(vertices)=={v for bag in part for v in bag}
        assert sum(map(len,part))==len(vertices)


if __name__ == "__main__":
    for n in (6,7):
        for h in (5,7):
            for isolated in (False,True):
                check(n,h,isolated)
    assert list(proposals([],[]))==[()]
    print("8 relabeled Kneser products incl isolates, empty graph passed")
