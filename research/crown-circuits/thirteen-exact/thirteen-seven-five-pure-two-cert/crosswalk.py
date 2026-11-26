"""Check both geometric obligations directly against the unquotiented model ledger."""
from collections import Counter
from pathlib import Path
root = Path(__file__).resolve().parent

def classify(vertices, edges, branches, quartets):
    for b in branches - quartets:
        if any(frozenset((b, v)) not in edges for v in quartets):
            return "disjoint"
    for v in quartets:
        component = {v}
        while True:
            new = component | {x for edge in edges if edge & component for x in edge}
            if new == component:
                break
            component = new
        if len(vertices - component) < 2:
            return "component"
    return "clean"

counts = Counter()
vertices = set(range(5))
for line in (root / "models.tsv").read_text().splitlines():
    p, graph, clean, branch_mask, quartet_mask, dirty = map(int, line.split())
    branches = {v for v in vertices if branch_mask >> v & 1}
    if len(branches) != 2:
        continue
    assert p == 5
    quartets = {v for v in vertices if quartet_mask >> v & 1}
    edges = {frozenset((i,j)) for i in range(5) for j in range(i)
             if graph >> (i*(i-1)//2+j) & 1}
    result = classify(vertices, edges, branches, quartets)
    if result == "clean":
        assert not quartets and dirty == 0
    counts[result] += 1
assert sum(counts.values()) == 608 and counts["clean"] == 304
print("Original decorations", sorted(counts.items()))
historical = Counter()
for line in (root / "historical/component-cover.tsv").read_text().splitlines():
    geom, q, d, *fields = map(int, line.split())
    vertices = {0,1,3,4,5}
    quartets = {v for v in vertices if q >> v & 1}
    edges = {frozenset(v for v in vertices if label >> v & 1)
             for label in fields[:13] if label.bit_count() == 2}
    assert classify(vertices, edges, {0,1}, quartets) == "disjoint"
    historical[d.bit_count()] += 1
assert historical == {1:29,2:44}
print("Historical pending rows by private dirty count", sorted(historical.items()))
