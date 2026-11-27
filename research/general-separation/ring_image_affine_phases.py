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


def certified_phases(n, clauses, point, k):
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
    root, _ = reconstructed
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
    return dict(status="certified", arity=arity, formula=formula,
                phase_count=len(components), edge_literals=phases, rows=tuple(rows))


def _insert(basis, mask, rhs):
    while mask:
        i = mask.bit_length()-1
        if i not in basis:
            basis[i] = mask, rhs
            return True
        a, b = basis[i]
        mask, rhs = mask ^ a, rhs ^ b
    return rhs == 0


def _solution(basis, seed=0):
    word = seed
    for i in sorted(basis):
        row, rhs = basis[i]
        if ((row & word).bit_count() & 1) != rhs:
            word ^= 1 << i
    return word


def _affine_groups(rows, variables):
    groups = {}
    for row in rows:
        support = tuple(sorted(abs(x) for x in row))
        negatives = {-x for x in row if x < 0}
        forbidden = sum(1 << j for j, x in enumerate(support) if x in negatives)
        groups.setdefault(support, set()).add(forbidden)
    joint = {}
    contradiction = False
    for support, forbidden in groups.items():
        width = len(support)
        size = 1 << width
        if size > 2*len(forbidden):
            return "unknown", None
        allowed = [x for x in range(size) if x not in forbidden]
        if not allowed:
            contradiction = True
            continue
        origin = allowed[0]
        directions = {}
        for x in allowed:
            _insert(directions, x ^ origin, 0)
        if len(allowed) != 1 << len(directions):
            return "unknown", None
        # Nullspace of the direction rows gives the annihilating equations.
        for j in range(width):
            if j in directions:
                continue
            normal = _solution(directions, 1 << j)
            mask = sum(1 << (v-1) for pos, v in enumerate(support) if normal & (1 << pos))
            rhs = (normal & origin).bit_count() & 1
            if not _insert(joint, mask, rhs):
                contradiction = True
    if contradiction:
        return "zero", None
    word = _solution(joint)
    return "nonzero", [(word >> i) & 1 for i in range(variables)]


def decide(n, clauses, point, k):
    import networkx as nx
    chart = certified_phases(n, clauses, point, k)
    if chart["status"] != "certified":
        return chart
    rows, count = chart["rows"], chart["phase_count"]
    if all(len(row) <= 2 for row in rows):
        bits = _two_sat(nx, count, rows)
        if bits is None:
            return dict(status="zero")
    else:
        status, bits = _affine_groups(rows, count)
        if status == "unknown":
            return dict(status=status, reason="nonaffine_phase_group")
        if status == "zero":
            return dict(status=status)
    phases = chart["edge_literals"]
    assignment = [0]*chart["arity"]
    for x, lit in phases.items():
        assignment[x-1] = int(bits[abs(lit)-1] == (lit > 0))
    if not all(any(assignment[abs(x)-1] == (x > 0) for x in row) for row in chart["formula"]):
        raise AssertionError("invalid reconstructed source witness")
    return dict(status="nonzero", assignment=tuple(assignment))


solve = decide
