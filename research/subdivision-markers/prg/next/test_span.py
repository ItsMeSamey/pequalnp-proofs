from random import Random
from span import compute

r = Random(418)
for k in range(500):
    n = r.randrange(9)
    flats = [[(r.randrange(1 << n),r.randrange(2)) for _ in range(r.randrange(7))]
             for _ in range(r.randrange(1,12))]
    nodes = list(range(len(flats)))
    r.shuffle(nodes)
    while len(nodes)>1:
        l = nodes.pop(r.randrange(len(nodes)))
        h = nodes.pop(r.randrange(len(nodes)))
        nodes.append((l,h))
    tree = nodes[0]
    def valid(x):
        return all(any(((x&m).bit_count()%2) != c for m,c in f) for f in flats)
    expected = sum(valid(x) for x in range(1 << n))
    assert compute(n,flats,tree) == expected
    w = compute(n,flats,tree,True)
    assert (w is None) == (expected == 0)
    assert w is None or valid(w)
print("500 exact counts and witness checks passed")
