"""Evaluate all conserved colorings on the six unsubdivided K4 edges."""
from itertools import combinations, product

edges = list(combinations(range(4), 2))
for length in (4, 5, 12):
    raw = exact = 1000
    for colors in product(range(4), repeat=6):
        boundary = [0]*4
        for (a, b), color in zip(edges, colors):
            boundary[a] ^= color
            boundary[b] ^= color
        if any(boundary):
            continue
        triangle = colors[edges.index((0, 1))] ^ colors[edges.index((2, 3))]
        zero_edges = [e for e, c in zip(edges, colors) if c == 0]
        count = length * len(zero_edges) + 3 * (triangle == 0)
        raw = min(raw, count)
        if triangle == 0:
            continue
        components = [{i} for i in range(4)]
        for a, b in zero_edges:
            ca = next(comp for comp in components if a in comp)
            cb = next(comp for comp in components if b in comp)
            if ca == cb:
                break
            components.remove(ca)
            components.remove(cb)
            components.append(ca | cb)
        else:
            exact = min(exact, count)
    assert (raw, exact) == (3, length)
    print(length, raw, exact)
