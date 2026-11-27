"""Exhaustively compare the common-exterior criterion and cube rows on four sites."""
from itertools import combinations, product
from math import comb


def connected(vertices, adjacency):
    if not vertices:
        return False
    seen = {min(vertices)}
    pending = list(seen)
    while pending:
        new = (adjacency[pending.pop()] & vertices) - seen
        pending.extend(new)
        seen.update(new)
    return seen == vertices


def compare(n, p, degree):
    nodes = set(range(n))
    edges = list(combinations(range(n), 2))
    tested = certified = 0
    supports = [s for size in range(degree + 1) for s in combinations(range(n), size)]
    monomials = [list(zip(s, colors)) for s in supports
                 for colors in product(range(1, p), repeat=len(s))]
    for mask in range(1 << len(edges)):
        adjacency = [set() for _ in nodes]
        for i, (u, v) in enumerate(edges):
            if mask & (1 << i):
                adjacency[u].add(v)
                adjacency[v].add(u)
        feasible = {x for x in product(range(p), repeat=n)
                    if all(connected({i for i in nodes if x[i] == c}, adjacency)
                           for c in range(p))}
        sample = []
        for s in supports:
            outside = sorted(nodes - set(s))
            chosen = None
            for exterior in product(range(p), repeat=len(outside)):
                fixed = dict(zip(outside, exterior))
                parts = [{v for v in outside if fixed[v] == c} for c in range(p)]
                criterion = all(connected(part, adjacency) and
                                all(adjacency[v] & part for v in s) for part in parts)
                cube = []
                for colors in product(range(p), repeat=len(s)):
                    assignment = fixed | dict(zip(s, colors))
                    cube.append(tuple(assignment[v] for v in range(n)))
                assert criterion == all(x in feasible for x in cube)
                if criterion and chosen is None:
                    chosen = cube
            sample.append(chosen)
        tested += 1
        if None in sample:
            continue
        certified += 1
        pivots = {}
        for cube in sample:
            for x in cube:
                row = sum(1 << i for i, m in enumerate(monomials)
                          if all(x[v] == c for v, c in m))
                while row and row.bit_length() in pivots:
                    row ^= pivots[row.bit_length()]
                if row:
                    pivots[row.bit_length()] = row
        assert len(pivots) == sum(comb(n, j) * (p - 1)**j for j in range(degree + 1))
    return tested, certified


if __name__ == "__main__":
    for params in [(4, 2, 2), (4, 3, 1)]:
        print(params, compare(*params))
