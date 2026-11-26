"""Verify the direct-shift construction with K_{3,2} and K_5."""
from collections import Counter
from itertools import combinations


def bit(i):
    return 1 << i


def parity(mask):
    return mask.bit_count() % 2


def obeys(value, row):
    pivot, mask, offset = row
    return not (value & bit(pivot)) or parity(value & mask) == offset


# The four non-first edges are (1,0), (2,0), (0,1), (2,1).
# The first edges are (0,0) and (1,1); the shifted edge is (2,0).
base = [(0, bit(2), 1), (1, bit(2) | bit(0), 1),
        (2, bit(0), 1), (3, bit(0) | bit(2), 1)]
root = 4
old = base.copy()
old[1] = (1, old[1][1] | bit(root), 1)
marker = bit(1) | bit(3)
edges = list(combinations(range(5), 2))
incident = [sum(bit(9+i) for i, edge in enumerate(edges) if v in edge)
            for v in range(5)]
gadget = [(4+v, mask, int(v == 0)) for v, mask in enumerate(incident)]
gadget += [(9+i, bit(4+u) | bit(4+v), 0) for i, (u,v) in enumerate(edges)]
rows = old + gadget
for value in range(1 << 19):
    bad = sum(not obeys(value, row) for row in gadget)
    assert bad % 2 == bool(value & bit(root))
    if bad == 0 and parity(value & marker):
        assert any(not obeys(value, row) for row in old)
    if value < 16:
        assert all(obeys(value, row) for row in gadget)
        assert [obeys(value, r) for r in old] == [obeys(value, r) for r in base]

# Plant x=e and a_v=1. Enumerate the full solutions for each defect.
fixed = bit(1) | sum(bit(4+v) for v in range(5))
solutions = [[] for v in range(5)]
for z in range(1 << 10):
    value = fixed | (z << 9)
    syndrome = sum(bit(v) for v, mask in enumerate(incident)
                   if parity(value & mask) != (v == 0))
    if syndrome.bit_count() == 1:
        solutions[syndrome.bit_length()-1].append(value)
assert {len(fiber) for fiber in solutions} == {64}


def giant(mask):
    unseen = set(range(5))
    while unseen:
        component = {unseen.pop()}
        queue = list(component)
        while queue:
            v = queue.pop()
            for i, edge in enumerate(edges):
                if v in edge and not mask & bit(9+i):
                    for w in edge:
                        if w in unseen:
                            unseen.remove(w)
                            component.add(w)
                            queue.append(w)
        if len(component) > 2:
            return component
    raise AssertionError("missing giant")


scopes = [bit(p) | m for p, m, _ in rows]
marginals = {}
for width in range(6):
    for indexes in combinations(range(10), width):
        mask = sum(bit(9+i) for i in indexes)
        defects = giant(mask)
        counts = Counter(value & mask for value in solutions[min(defects)])
        for v in defects:
            assert counts == Counter(value & mask for value in solutions[v])
        for i in indexes:
            child = mask ^ bit(9+i)
            projection = Counter()
            for assignment, multiplicity in counts.items():
                projection[assignment & child] += multiplicity
            assert projection == marginals[child]
        marginals[mask] = counts
        for assignment in counts:
            point = fixed | assignment
            assert parity(point & marker)
            for scope, row in zip(scopes, rows):
                if (scope >> 9) & ~(mask >> 9) == 0:
                    assert obeys(point, row)
print("524288 full assignments and 638 exact edge marginals through width five passed.")
