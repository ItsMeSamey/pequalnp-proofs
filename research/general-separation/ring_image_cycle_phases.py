"""Ordered ring-image decision by recovering even-cycle matching phases.

Public decide(n,clauses,point,k) / solve accept the original four fields.
Only positive demand rows and distinct negative binary conflicts enter this
oriented fragment. The witnessed nonzero status carries original source bits.
The graph after deleting bridges retains ALL its vertices for the cycle test.
"""
from read_two_ring_image import recover
from ring_image_clique_matching import _root


def _two_sat(nx, variables, rows):
    implications = nx.DiGraph()
    for i in range(1, variables+1):
        implications.add_nodes_from((i, -i))
    for row in rows:
        if not row:
            return None
        a, b = row[0], row[-1]
        implications.add_edges_from(((-a, b), (-b, a)))
    condensed = nx.condensation(implications)
    component = condensed.graph["mapping"]
    order = {c: j for j, c in enumerate(nx.topological_sort(condensed))}
    bits = []
    for i in range(1, variables+1):
        if component[i] == component[-i]:
            return None
        bits.append(int(order[component[i]] > order[component[-i]]))
    if not all(any(bits[abs(i)-1] == (i > 0) for i in row) for row in rows):
        raise AssertionError("invalid phase model")
    return bits


def decide(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    import networkx as nx

    arity, formula = source
    conflict = nx.Graph()
    conflict.add_nodes_from(range(1, arity+1))
    demands = []
    for row in formula:
        if all(lit > 0 for lit in row):
            demands.append(frozenset(row))
        elif len(row) == 2 and all(lit < 0 for lit in row) and row[0] != row[1]:
            conflict.add_edge(-row[0], -row[1])
        else:
            return dict(status="unknown", reason="clause_syntax")
    reconstructed = _root(nx, conflict)
    if reconstructed is None:
        return dict(status="unknown", reason="line_graph")
    root, edges = reconstructed
    demanded = set(demands)
    for u in root:
        star = frozenset(root[u][v]["variable"] for v in root[u])
        if star not in demanded:
            return dict(status="unknown", reason="missing_star")

    # Each bridge separates a union of complete even components on each side
    # once the following certification succeeds. It cannot match across the cut.
    cycles = root.copy()
    cycles.remove_edges_from(list(nx.bridges(root)))
    components = sorted(nx.connected_components(cycles), key=min)
    phases = {}
    for i, comp in enumerate(components, 1):
        if len(comp) < 4 or len(comp) % 2 or any(cycles.degree(v) != 2 for v in comp):
            return dict(status="unknown", reason="noncycle_component")
        start = min(comp)
        u, v = start, min(cycles[start])
        for j in range(len(comp)):
            phases[cycles[u][v]["variable"]] = i if j % 2 == 0 else -i
            u, v = v, next(w for w in cycles[v] if w != u)
        if u != start:
            raise AssertionError("invalid cycle traversal")

    rows = []
    for demand in demands:
        row = {phases[x] for x in demand if x in phases}
        if any(-i in row for i in row):
            continue
        rows.append(tuple(sorted(row)))
    if any(len(row) > 2 for row in rows):
        return dict(status="unknown", reason="wide_phase_clause")
    bits = _two_sat(nx, len(components), rows)
    if bits is None:
        return dict(status="zero")
    assignment = [0]*arity
    for x in edges:
        if x in phases:
            lit = phases[x]
            assignment[x-1] = int(bits[abs(lit)-1] == (lit > 0))
    if not all(any(assignment[abs(x)-1] == (x > 0) for x in row) for row in formula):
        raise AssertionError("invalid reconstructed source witness")
    return dict(status="nonzero", assignment=tuple(assignment))


solve = decide
