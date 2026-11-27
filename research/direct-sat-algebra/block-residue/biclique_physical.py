"""Solve signed paired comparisons whose surviving conflict components are bicliques."""

from balanced_block import _potentials
from biclique_period import biclique_period_witness


class UnsupportedConflict(ValueError):
    """A surviving component is not complete bipartite."""


def _shores(neighbors, forced, new_index):
    colors = {}
    components = []
    for root in new_index:
        if root in colors:
            continue
        colors[root] = 0
        shores = [[], []]
        pending = [root]
        incidences = 0
        while pending:
            x = pending.pop()
            color = colors[x]
            shores[color].append(new_index[x])
            for y in neighbors[x]:
                if y in forced:
                    continue
                incidences += 1
                if y not in colors:
                    colors[y] = 1 ^ color
                    pending.append(y)
                elif colors[y] == color:
                    raise UnsupportedConflict("nonbipartite flag conflicts")
        if incidences != 2 * len(shores[0]) * len(shores[1]):
            raise UnsupportedConflict("missing cross-shore conflict")
        if incidences:
            components.append(tuple(shores))
    return components


def _cycle_columns(vertices, atoms):
    """One check per chord. A tree edge separates the chords crossing its cut."""
    adjacency = [[] for _ in range(vertices)]
    for i, (u, v, _) in enumerate(atoms):
        adjacency[u].append((v, i))
        adjacency[v].append((u, i))
    parent = [-1] * vertices
    incoming = [-1] * vertices
    order = []
    tree = set()
    for root in range(vertices):
        if parent[root] != -1:
            continue
        parent[root] = root
        pending = [root]
        while pending:
            u = pending.pop()
            order.append(u)
            for v, edge in adjacency[u]:
                if parent[v] == -1:
                    parent[v] = u
                    incoming[v] = edge
                    tree.add(edge)
                    pending.append(v)
    columns = [0] * len(atoms)
    cuts = [0] * vertices
    bit = 1
    for i, (u, v, _) in enumerate(atoms):
        if i not in tree:
            columns[i] = bit
            cuts[u] ^= bit
            cuts[v] ^= bit
            bit <<= 1
    for v in reversed(order):
        if incoming[v] != -1:
            columns[incoming[v]] = cuts[v]
            cuts[parent[v]] ^= cuts[v]
    return columns


def biclique_comparison_witness(vertices, comparisons):
    """Return original vertex bits or None. Consecutive comparisons form a shell."""
    edges = tuple(comparisons)
    if not isinstance(vertices, int) or vertices < 0 or len(edges) % 2:
        raise ValueError("expected nonnegative order and paired comparisons")
    atoms = []
    indices = {}
    occurrences = []
    for u, v, sign in edges:
        if not (0 <= u < vertices and 0 <= v < vertices and sign in (0, 1)):
            raise ValueError("invalid signed comparison")
        atom = (min(u, v), max(u, v), sign)
        if atom not in indices:
            indices[atom] = len(atoms)
            atoms.append(atom)
        occurrences.append(indices[atom])

    forced = set()
    neighbors = [set() for _ in atoms]
    for a, b in zip(occurrences[::2], occurrences[1::2]):
        if a == b:
            forced.add(a)
        else:
            neighbors[a].add(b)
            neighbors[b].add(a)
    survivors = [i for i in range(len(atoms)) if i not in forced]
    new_index = {old: new for new, old in enumerate(survivors)}
    components = _shores(neighbors, forced, new_index)
    columns = _cycle_columns(vertices, atoms)
    target = 0
    for column, (_, _, sign) in zip(columns, atoms):
        if sign:
            target ^= column
    flags = biclique_period_witness([columns[i] for i in survivors], target, components)
    if flags is None:
        return None

    signed = [[] for _ in range(vertices)]
    for i, (u, v, sign) in enumerate(atoms):
        difference = sign if i in forced else sign ^ flags[new_index[i]]
        signed[u].append((v, difference))
        signed[v].append((u, difference))
    lifted = _potentials(signed)
    if lifted is None:
        raise AssertionError("cycle syndrome failed to lift")
    values = lifted[1]
    met = [values[u] ^ values[v] == sign for u, v, sign in edges]
    if not all(a or b for a, b in zip(met[::2], met[1::2])):
        raise AssertionError("original paired comparison replay failed")
    return values


def biclique_block_witness(shells, pins):
    """Return physical color bits, including the signed copy offsets."""
    if not isinstance(shells, int) or shells < 0:
        raise ValueError("expected a nonnegative shell count")
    n = 4 * shells
    graph = [[] for _ in range(n)]
    pins = tuple(pins)
    for a, b, sign in pins:
        if not (0 <= a < n and 0 <= b < n and sign in (0, 1)):
            raise ValueError("invalid signed pin")
        graph[a].append((b, sign))
        graph[b].append((a, sign))
    contracted = _potentials(graph)
    if contracted is None:
        return None
    roots, offsets = contracted
    edges = []
    for a in range(n):
        if a % 4 < 2:
            b = a + 2
            edges.append((roots[a], roots[b], 1 ^ offsets[a] ^ offsets[b]))
    model = biclique_comparison_witness(n, edges)
    if model is None:
        return None
    raw = [model[root] ^ offset for root, offset in zip(roots, offsets)]
    if not all(raw[a] ^ raw[b] == sign for a, b, sign in pins):
        raise AssertionError("physical copy pin replay failed")
    if any(raw[a:a+2] == raw[a+2:a+4] for a in range(0, n, 4)):
        raise AssertionError("physical matching edge replay failed")
    return raw
