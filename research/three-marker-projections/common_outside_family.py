"""Construct graph-only physical moment witnesses via bounded exterior cores."""
from itertools import combinations, product
from mim_moment_family import _components, _add_independent


def common_outside_family(n, edges, colors, degree, *, max_core_size=2, reduce=True):
    """Return (actual_colorings, None) or (None, failed_test_set).

    The search is exact for exterior cores of at most max_core_size sites
    each, followed by unrestricted connected flood completion. A failed set
    does not rule out larger cores or another moment construction. With
    reduce=True the returned GF(2) moment rows are independent. False keeps
    whole cubes, needed for predicates outside the degree-D polynomial span.
    """
    if min(n, colors, max_core_size) < 1 or degree < 0:
        raise ValueError("Invalid size, color count, degree or core cap")
    vertices = set(range(n))
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        if u not in vertices or v not in vertices:
            raise ValueError("Edge endpoint is outside the graph")
        if u != v:
            neighbors[u].add(v)
            neighbors[v].add(u)
    if colors == 1:
        return ([(0,) * n], None) if len(list(_components(vertices, neighbors))) == 1 else (None, ())
    width = min(degree, n)
    witnesses = []
    pivots = {}
    for test in combinations(range(n), width):
        outside = vertices - set(test)
        components = list(_components(outside, neighbors))
        if len(outside) < colors or len(components) > colors:
            return None, test
        candidates = []
        for size in range(1, min(max_core_size, len(outside)) + 1):
            for sites in combinations(sorted(outside), size):
                core = frozenset(sites)
                if (all(neighbors[v] & core for v in test)
                        and len(list(_components(core, neighbors))) == 1):
                    candidates.append(core)
        selected = None
        for cores in combinations(candidates, colors):
            occupied = set().union(*cores)
            if len(occupied) == sum(map(len, cores)) and all(occupied & part for part in components):
                selected = cores
                break
        if selected is None:
            return None, test
        assignment = [-1] * n
        frontier = []
        for color, core in enumerate(selected):
            for v in core:
                assignment[v] = color
                frontier.append(v)
        while frontier:
            u = frontier.pop()
            for v in neighbors[u] & outside:
                if assignment[v] == -1:
                    assignment[v] = assignment[u]
                    frontier.append(v)
        for coloring in product(range(colors), repeat=width):
            for v, color in zip(test, coloring):
                assignment[v] = color
            if reduce:
                active = [(v, c) for v, c in enumerate(assignment) if c != colors-1]
                row = {term for size in range(min(degree, len(active)) + 1)
                       for term in combinations(active, size)}
                if not _add_independent(pivots, row):
                    continue
            witnesses.append(tuple(assignment))
    return witnesses, None
