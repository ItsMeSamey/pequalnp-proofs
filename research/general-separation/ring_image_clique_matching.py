"""Ordered unsigned ring image, negative conflicts and positive clique demands."""
from itertools import combinations
from read_two_ring_image import recover


def _root(nx, conflict):
    """Name each root edge by its unique shared original variable."""
    root = nx.Graph()
    edges = {}
    for component in nx.connected_components(conflict):
        offset = len(root)
        if len(component) == 1:
            x, = component
            edges[x] = (offset, offset+1)
            root.add_edge(offset, offset+1, variable=x)
            continue
        try:
            inverse = nx.inverse_line_graph(conflict.subgraph(component))
        except nx.NetworkXError:
            return None
        ids = {v: offset+i for i, v in enumerate(inverse)}
        for left, right in inverse.edges:
            common = set(left).intersection(right)
            if len(common) != 1:
                return None
            x, = common
            if x not in component or x in edges:
                return None
            edge = (ids[left], ids[right])
            root.add_edge(*edge, variable=x)
            edges[x] = edge
    if set(edges) != set(conflict) or len(edges) != root.number_of_edges():
        return None
    for x, y in combinations(edges, 2):
        intersect = bool(set(edges[x]).intersection(edges[y]))
        if intersect != conflict.has_edge(x, y):
            return None
    return root, edges


def decide(n, clauses, point, k):
    """Return off_image, unknown, zero, or nonzero with a source assignment."""
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    import networkx as nx

    a, formula = source
    conflict = nx.Graph()
    conflict.add_nodes_from(range(1, a+1))
    demands = []
    for row in formula:
        if all(lit > 0 for lit in row):
            demands.append(row)
        elif len(row) == 2 and all(lit < 0 for lit in row):
            conflict.add_edge(-row[0], -row[1])
        else:
            return dict(status="unknown", reason="clause_syntax")
    for row in demands:
        if any(not conflict.has_edge(i, j) for i, j in combinations(row, 2)):
            return dict(status="unknown", reason="nonclique")
    reconstructed = _root(nx, conflict)
    if reconstructed is None:
        return dict(status="unknown", reason="line_graph")
    root, edges = reconstructed
    weights = dict.fromkeys(edges, 0)
    for row in demands:
        for x in row:
            weights[x] += 1
    for x, (u, v) in edges.items():
        root[u][v]["weight"] = weights[x]
    matching = nx.max_weight_matching(root, maxcardinality=False, weight="weight")
    chosen = {root[u][v]["variable"] for u, v in matching}
    score = sum(weights[x] for x in chosen)
    if score != len(demands):
        return dict(status="zero", covered=score, required=len(demands))
    assignment = tuple(int(x in chosen) for x in range(1, a+1))
    if not all(any(assignment[abs(lit)-1] == (lit > 0) for lit in row)
               for row in formula):
        raise AssertionError("matching witness fails recovered formula")
    return dict(status="nonzero", assignment=assignment,
                covered=score, required=len(demands))
