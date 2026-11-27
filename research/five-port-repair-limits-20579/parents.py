"""Enumerate maximal-rectangle covers of the fixed residual in the ambient graph."""
from functools import reduce
from hashlib import sha256
from itertools import combinations
import json
from operator import or_


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def parent_covers(rows, residual, packing):
    """Return the canonical list of ten-rectangle parents for this instance."""
    if len(rows) != 32 or any(type(r) is not int or not 0 <= r < 2**32 for r in rows):
        raise ValueError("expected 32 unsigned row masks")
    cells = sorted(residual)
    if len(cells) != 98 or any(not (0 <= r < 32 and 0 <= c < 32 and rows[r] >> c & 1)
                               for r, c in cells):
        raise ValueError("invalid residual")
    points = list(map(tuple, packing))
    if len(points) != 10 or len(set(points)) != 10 or not set(points) <= residual:
        raise ValueError("invalid packing")
    for (r, c), (s, t) in combinations(points, 2):
        if rows[r] >> t & 1 and rows[s] >> c & 1:
            raise ValueError("packing points share a rectangle")

    columns = {2**32 - 1}
    for row in rows:
        columns |= {col & row for col in columns}
    rectangles = []
    for col in columns - {0}:
        extent = sum(1 << r for r, row in enumerate(rows) if row & col == col)
        if extent:
            rectangles.append((extent, col))
    rectangles.sort()
    if len(rectangles) != 1893:
        raise ValueError("unexpected ambient rectangle count")

    supports = {(r, c): sum(1 << i for i, (a, b) in enumerate(rectangles)
                           if a >> r & 1 and b >> c & 1) for r, c in cells}
    solutions = []
    def visit(domains):
        while True:
            possible = reduce(or_, domains)
            for support in supports.values():
                available = possible & support
                if not available:
                    return
                owners = [i for i, domain in enumerate(domains) if available & domain]
                if len(owners) == 1 and domains[owners[0]] != available:
                    domains[owners[0]] = available
                    break
            else:
                break
        choices = [i for i, domain in enumerate(domains) if domain.bit_count() > 1]
        if not choices:
            solutions.append(tuple(sorted(rectangles[d.bit_length() - 1] for d in domains)))
            return
        i = min(choices, key=lambda j: domains[j].bit_count())
        for bit in bits(domains[i]):
            child = domains.copy()
            child[i] = 1 << bit
            visit(child)

    visit([supports[p] for p in points])
    solutions.sort()
    digest = sha256(json.dumps(solutions, separators=(',', ':')).encode()).hexdigest()
    if len(solutions) != 214 or digest != 'e90533581166719b9694469b56dfc4dc00f99d8e5c3f6f8c1d977155bfda5133':
        raise ValueError("parent count or canonical digest mismatch")
    return solutions
