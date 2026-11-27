"""GF(2) span of augmented perfect matchings in indexed loopless multigraphs."""

from general_blossom import maximum_cardinality_matching
from tight_cut import tight_shore


def _kernel(rows, width):
    """Return a right-nullspace basis of integer bit rows."""
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    ordered = sorted(pivots.items())
    basis = []
    for free in range(width):
        if free in pivots:
            continue
        vector = 1 << free
        for pivot, row in ordered:
            if (vector & row).bit_count() % 2:
                vector |= 1 << pivot
        basis.append(vector)
    return basis


def _components(vertices, edges):
    neighbors = {v: set() for v in vertices}
    for u, v in edges.values():
        neighbors[u].add(v)
        neighbors[v].add(u)
    remaining = set(vertices)
    while remaining:
        start = min(remaining)
        color = {start: 0}
        pending = [start]
        bipartite = True
        while pending:
            u = pending.pop()
            for v in neighbors[u]:
                if v not in color:
                    color[v] = 1 - color[u]
                    pending.append(v)
                elif color[v] == color[u]:
                    bipartite = False
        remaining.difference_update(color)
        yield set(color), bipartite


def _contract_other_side(shore, vertices, edges):
    marker = min(vertices - shore)
    retained = {}
    for index, (u, v) in edges.items():
        if u in shore or v in shore:
            retained[index] = (u if u in shore else marker,
                               v if v in shore else marker)
    return shore | {marker}, retained


def _small_node_equations(vertices, edges, cbit):
    # Collapse each parallel class to its parity. Every pair of copies
    # differs by a two-edge vector in the span, since all edges are allowed.
    groups = {}
    for edge, (u, v) in edges.items():
        key = (min(u, v), max(u, v))
        groups[key] = groups.get(key, 0) | (1 << edge)
    neighbors = {v: [] for v in vertices}
    class_masks = list(groups.values())
    for j, (u, v) in enumerate(groups):
        neighbors[u].append((v, j))
        neighbors[v].append((u, j))

    def matchings(left, mask):
        if not left:
            yield mask
            return
        u = min(left)
        for v, j in neighbors[u]:
            if v in left:
                yield from matchings(left - {u, v}, mask | (1 << j))

    k = len(groups)
    for check in _kernel(matchings(vertices, 1 << k), k + 1):
        lifted = cbit if check & (1 << k) else 0
        for j, group in enumerate(class_masks):
            if check & (1 << j):
                lifted |= group
        yield lifted


def _has_matching(vertices, pairs):
    matched = maximum_cardinality_matching(vertices, pairs)
    return 2 * len(matched) == len(vertices)


def _hull(vertices, edges, width):
    cbit = 1 << width
    if not vertices:
        return [cbit]
    if not _has_matching(vertices, tuple(edges.values())):
        return []

    # All forced-zero coordinates must survive the final kernel calculation.
    allowed = {}
    equations = []
    for i in range(width):
        if i in edges:
            u, v = edges[i]
            left = vertices - {u, v}
            residual = tuple(pair for pair in edges.values()
                             if pair[0] in left and pair[1] in left)
            if _has_matching(left, residual):
                allowed[i] = (u, v)
                continue
        equations.append(1 << i)

    nodes = []
    for part, bipartite in _components(vertices, allowed):
        local = {i: pair for i, pair in allowed.items() if pair[0] in part}
        nodes.append((part, local, bipartite))
    while nodes:
        part, local, bipartite = nodes.pop()
        if not bipartite and len(part) <= 10:
            # Includes every Petersen brick, regardless of edge multiplicity.
            equations.extend(_small_node_equations(part, local, cbit))
            continue
        if not bipartite:
            shore = tight_shore(part, local.values(),
                                maximum_matching=maximum_cardinality_matching)
            if shore is not None:
                # Crossing edges retain their original IDs in both children.
                for side in (set(shore), part - set(shore)):
                    child, subedges = _contract_other_side(side, part, local)
                    _, is_bipartite = next(_components(child, subedges))
                    nodes.append((child, subedges, is_bipartite))
                continue
        stars = dict.fromkeys(part, cbit)
        total = cbit if (len(part) // 2) % 2 else 0
        for i, (u, v) in local.items():
            bit = 1 << i
            stars[u] |= bit
            stars[v] |= bit
            total |= bit
        equations.extend(stars.values())
        if not bipartite:
            equations.append(total)
    return _kernel(equations, width + 1)


def _indexed(vertices, edges):
    vertices = set(range(vertices) if isinstance(vertices, int) else vertices)
    indexed = {}
    for i, (u, v) in enumerate(edges):
        if u == v or u not in vertices or v not in vertices:
            raise ValueError("expected loopless edges with declared endpoints")
        indexed[i] = (u, v)
    return vertices, indexed


def matching_hull(vertices, edges):
    """Basis masks with edge bits 0..m-1 and homogenizing coordinate m.

    Vertices are integer IDs or an integer order. Edges are endpoint pairs
    in input order. A basis row may represent a sum of multiple matchings.
    """
    vertices, indexed = _indexed(vertices, edges)
    return _hull(vertices, indexed, len(indexed))


def parity_matching(vertices, edges, red_mask, parity):
    """Return an actual perfect matching edge mask of the given parity, or None."""
    vertices, indexed = _indexed(vertices, edges)
    width = len(indexed)
    if parity not in (0, 1) or not 0 <= red_mask < (1 << width):
        raise ValueError("invalid parity or edge mask")
    probe = red_mask | ((1 - parity) << width)

    def feasible(candidate):
        return any((row & probe).bit_count() % 2
                   for row in _hull(vertices, candidate, width))

    if not feasible(indexed):
        return None
    for edge in tuple(indexed):
        endpoints = indexed.pop(edge)
        if not feasible(indexed):
            indexed[edge] = endpoints
    return sum(1 << edge for edge in indexed)
