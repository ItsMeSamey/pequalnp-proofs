"""Exact ordered-image counting by planar perfect matchings and demand inclusion-exclusion."""
from itertools import pairwise
from read_two_ring_image import recover
from ring_image_clique_matching import _root


def _sign(nx, graph):
    planar, embedding = nx.check_planarity(graph)
    if not planar:
        return None
    face = {}
    rhs = []
    for u in embedding:
        for v in embedding[u]:
            if (u, v) in face:
                continue
            walk = embedding.traverse_face(u, v)
            for half in pairwise(walk + [walk[0]]):
                face[half] = len(rhs)
            rhs.append((len(walk)//2 + 1) % 2)
    dual = [[] for _ in rhs]
    for u, v, data in graph.edges(data=True):
        f, g = face[u, v], face[v, u]
        if f != g:
            x = data["variable"]
            dual[f].append((g, x))
            dual[g].append((f, x))
    parent = {0: None}
    order = [0]
    for f in order:
        for g, x in dual[f]:
            if g not in parent:
                parent[g] = (f, x)
                order.append(g)
    if len(order) != len(rhs):
        raise AssertionError("disconnected face dual")
    negative = set()
    for f in reversed(order[1:]):
        g, x = parent[f]
        if rhs[f]:
            negative.add(x)
            rhs[g] ^= 1
    return negative


def _det(a):
    """Absolute fraction-free determinant of a square integer matrix."""
    n = len(a)
    if not n:
        return 1
    previous = 1
    for j in range(n-1):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return 0
        a[j], a[pivot] = a[pivot], a[j]
        current = a[j][j]
        for i in range(j+1, n):
            for h in range(j+1, n):
                a[i][h] = (current*a[i][h] - a[i][j]*a[j][h]) // previous
        previous = current
    return abs(a[-1][-1])


def decide(n, clauses, point, k, *, max_determinants=None):
    if max_determinants is not None and (type(max_determinants) is not int or max_determinants < 0):
        raise ValueError("max_determinants must be a nonnegative integer")
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    import networkx as nx

    a, formula = source
    conflict = nx.Graph()
    conflict.add_nodes_from(range(1, a+1))
    demands = set()
    for row in formula:
        if all(i > 0 for i in row):
            demands.add(frozenset(row))
        elif len(row) == 2 and all(i < 0 for i in row):
            conflict.add_edge(-row[0], -row[1])
        else:
            return dict(status="unknown", reason="clause_syntax")
    inverse = _root(nx, conflict)
    if inverse is None:
        return dict(status="unknown", reason="line_graph")
    root, edges = inverse
    stars = {v: frozenset(data["variable"] for *_, data in root.edges(v, data=True))
             for v in root}
    if not set(stars.values()) <= demands:
        return dict(status="unknown", reason="missing_star")
    if not nx.is_bipartite(root):
        return dict(status="unknown", reason="nonbipartite")
    zero = dict(status="zero", count=0, value=0)
    negative = set()
    for comp in nx.connected_components(root):
        signs = _sign(nx, root.subgraph(comp))
        if signs is None:
            return dict(status="unknown", reason="nonplanar")
        negative.update(signs)
    if frozenset() in demands:
        return zero
    allowed = set(edges)
    extra = []
    for row in demands:
        centers = set.intersection(*(set(edges[x]) for x in row))
        if centers:
            for v in centers:
                allowed.difference_update(stars[v] - row)
        else:
            extra.append(row)
    defects = {frozenset(row & allowed) for row in extra}
    if frozenset() in defects:
        return zero
    defects = [row for row in defects if not any(other < row for other in defects)]
    color = nx.bipartite.color(root)
    left = {v: i for i, v in enumerate(v for v in root if color[v])}
    right = {v: i for i, v in enumerate(v for v in root if not color[v])}
    if len(left) != len(right):
        return zero
    entries = {}
    for x in allowed:
        u, v = edges[x]
        if u not in left:
            u, v = v, u
        entries[x] = (left[u], right[v], -1 if x in negative else 1)

    bound = (1 + len(allowed)) << len(defects)
    if max_determinants is not None and max_determinants < bound:
        return dict(status="unknown", reason="determinant_budget",
                    required=bound, available=max_determinants)

    def count(active):
        total = 0
        for mask in range(1 << len(defects)):
            live = active.copy()
            for i, row in enumerate(defects):
                if mask >> i & 1:
                    live.difference_update(row)
            matrix = [[0] * len(left) for _ in left]
            for x in live:
                i, j, weight = entries[x]
                matrix[i][j] = weight
            term = _det(matrix)
            total += -term if mask.bit_count() % 2 else term
        return total

    total = count(allowed)
    if total == 0:
        return zero
    for x in sorted(allowed):
        trial = allowed - {x}
        if count(trial) > 0:
            allowed = trial
    assignment = tuple(int(x in allowed) for x in range(1, a+1))
    if total < 0 or not all(any(assignment[abs(i)-1] == (i > 0) for i in row)
                            for row in formula):
        raise AssertionError("failed planar source witness")
    modulus = 3 ** k
    value = pow(-15, k-a-1, modulus) * total % modulus
    return dict(status="nonzero", assignment=assignment, count=total, value=value)
