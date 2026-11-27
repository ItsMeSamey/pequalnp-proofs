"""Total paired-comparison solver using grouped or indexed conflict charts."""

from balanced_block import _potentials
from biclique_dual import biclique_dual_witness
from biclique_physical import UnsupportedConflict, _cycle_columns, _shores


def _chart(edges):
    """Return signed chart edges, selectable positions, and disjoint shores."""
    atoms = []
    lookup = {}
    occurrence = []
    for x, y, sign in edges:
        key = min(x, y), max(x, y), sign
        if key not in lookup:
            lookup[key] = len(atoms)
            atoms.append(key)
        occurrence.append(lookup[key])

    forced = set()
    neighbors = [set() for _ in atoms]
    for a, b in zip(occurrence[::2], occurrence[1::2]):
        if a == b:
            forced.add(a)
        else:
            neighbors[a].add(b)
            neighbors[b].add(a)
    available = [i for i in range(len(atoms)) if i not in forced]
    new_index = {old: new for new, old in enumerate(available)}
    try:
        shores = _shores(neighbors, forced, new_index)
    except UnsupportedConflict:
        # Split every comparison occurrence. Parallel chart edges now enforce
        # the required dependencies among equal and opposite signed requests.
        pairs = [((i,), (i + 1,)) for i in range(0, len(edges), 2)]
        return edges, range(len(edges)), pairs
    return atoms, available, shores


def total_comparison_witness(vertices, comparisons):
    """Decide arbitrary consecutive signed-comparison pairs, returning vertex bits."""
    edges = tuple(comparisons)
    if not isinstance(vertices, int) or vertices < 0 or len(edges) % 2:
        raise ValueError("expected nonnegative order and paired comparisons")
    for x, y, d in edges:
        if not (0 <= x < vertices and 0 <= y < vertices and d in (0, 1)):
            raise ValueError("invalid signed comparison")
    chart, available, shores = _chart(edges)
    columns = _cycle_columns(vertices, chart)
    target = 0
    for column, (_, _, d) in zip(columns, chart):
        if d:
            target ^= column
    flags = biclique_dual_witness([columns[i] for i in available], target, shores)
    if flags is None:
        return None
    failures = {i for i, bit in zip(available, flags) if bit}
    graph = [[] for _ in range(vertices)]
    for i, (x, y, d) in enumerate(chart):
        difference = d ^ (i in failures)
        graph[x].append((y, difference))
        graph[y].append((x, difference))
    lifted = _potentials(graph)
    if lifted is None:
        raise AssertionError("chart syndrome failed to integrate")
    values = lifted[1]
    met = [values[x] ^ values[y] == d for x, y, d in edges]
    if not all(left or right for left, right in zip(met[::2], met[1::2])):
        raise AssertionError("original shell replay failed")
    return values


def total_block_witness(shells, pins):
    """Decide arbitrary physical four-bit matching shells with signed copy pins."""
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
    for start in range(0, n, 4):
        for a in (start, start + 1):
            b = a + 2
            edges.append((roots[a], roots[b], 1 ^ offsets[a] ^ offsets[b]))
    values = total_comparison_witness(n, edges)
    if values is None:
        return None
    raw = [values[root] ^ offset for root, offset in zip(roots, offsets)]
    if not all(raw[a] ^ raw[b] == sign for a, b, sign in pins):
        raise AssertionError("original copy pin replay failed")
    if any(raw[a:a + 2] == raw[a + 2:a + 4] for a in range(0, n, 4)):
        raise AssertionError("original matching replay failed")
    return raw
