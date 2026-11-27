"""Enumerate all orientations giving a seven-star partition of the issued graph."""
from collections import Counter
from itertools import product

edges = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
left = {0,1,2,6,7}
counts = Counter()
for assignment in product((0,1), repeat=len(edges)):
    stars = {}
    for edge, endpoint in zip(edges, assignment):
        stars.setdefault(edge[endpoint], set()).add(edge[1-endpoint])
    if len(stars) != 7:
        continue
    products_mixed = operands_mixed = 0
    pure_output_sides = set()
    for center, leaves in stars.items():
        side = center in left
        sides = {v in left for v in leaves}
        if sides == {side}:
            pure_output_sides.add(side)
            continue
        products_mixed += 1
        operands_mixed += len(sides) == 2
    collector_mixed = products_mixed + len(pure_output_sides) - 1
    counts[products_mixed + operands_mixed + collector_mixed] += 1
print(sorted(counts.items()), sum(counts.values()))
assert counts == {13:20,14:12,15:252,16:136,17:652,18:388,19:28}
