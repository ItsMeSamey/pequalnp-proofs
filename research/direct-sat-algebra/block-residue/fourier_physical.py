"""Exact indexed-shell counts with original potential and signed-copy witnesses."""
from balanced_block import _potentials
from biclique_physical import _cycle_columns
from syndrome_fourier import fourier_count_witness


def comparison_count_witness(vertices, comparisons):
    """Count assignments of all declared vertices. Consecutive edges form shells."""
    edges = tuple(comparisons)
    if not isinstance(vertices, int) or vertices < 0 or len(edges) % 2:
        raise ValueError("expected nonnegative order and paired comparisons")
    for x, y, d in edges:
        if not (0 <= x < vertices and 0 <= y < vertices and d in (0, 1)):
            raise ValueError("invalid signed comparison")
    columns = _cycle_columns(vertices, edges)
    target = 0
    for h, (_, _, d) in zip(columns, edges):
        if d:
            target ^= h
    shores = [((i,), (i + 1,)) for i in range(0, len(edges), 2)]
    count, flags = fourier_count_witness(columns, target, shores)
    if count == 0:
        if flags is not None:
            raise AssertionError("zero count returned a witness")
        return 0, None
    if flags is None or len(flags) != len(edges):
        raise AssertionError("missing indexed failure flags")

    graph = [[] for _ in range(vertices)]
    for (x, y, d), failed in zip(edges, flags):
        difference = d ^ failed
        graph[x].append((y, difference))
        graph[y].append((x, difference))
    integrated = _potentials(graph)
    if integrated is None:
        raise AssertionError("counted syndrome failed to integrate")
    roots, values = integrated
    satisfied = [values[u] ^ values[v] == d for u, v, d in edges]
    if not all(a or b for a, b in zip(satisfied[::2], satisfied[1::2])):
        raise AssertionError("original shell replay failed")
    # The same flag vector lifts once per component-root assignment. A
    # declared isolated vertex forms a component of its own.
    return count << len(set(roots)), values


def block_count_witness(shells, pins):
    """Count assignments of the four raw bits per shell after signed copy pins."""
    if not isinstance(shells, int) or shells < 0:
        raise ValueError("expected a nonnegative shell count")
    size = 4 * shells
    pins = tuple(pins)
    graph = [[] for _ in range(size)]
    for a, b, d in pins:
        if not (0 <= a < size and 0 <= b < size and d in (0, 1)):
            raise ValueError("invalid signed pin")
        graph[a].append((b, d))
        graph[b].append((a, d))
    pin_solution = _potentials(graph)
    if pin_solution is None:
        return 0, None
    roots, offsets = pin_solution
    # Only actual pin-equivalence classes have assignment bits. A representative
    # plus its offsets determines all raw bits in its class bijectively.
    names = {root: i for i, root in enumerate(dict.fromkeys(roots))}
    ids = [names[r] for r in roots]
    edges = []
    for start in range(0, size, 4):
        for a in (start, start + 1):
            b = a + 2
            edges.append((ids[a], ids[b], 1 ^ offsets[a] ^ offsets[b]))
    count, values = comparison_count_witness(len(names), edges)
    if not count:
        return 0, None
    raw = [values[i] ^ d for i, d in zip(ids, offsets)]
    if not all(raw[a] ^ raw[b] == d for a, b, d in pins):
        raise AssertionError("original signed pin replay failed")
    if any(raw[a:a + 2] == raw[a + 2:a + 4] for a in range(0, size, 4)):
        raise AssertionError("original physical shell replay failed")
    return count, raw
