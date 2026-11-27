"""Seed the original signed-shell solver with certified incident directions."""

from balanced_block import _potentials
from biclique_dual import biclique_dual_witness
from biclique_period import _basis, _reduce
from biclique_physical import _cycle_columns
from biclique_total import total_comparison_witness
from incident_port import forest_chords, incident_directions


def _transport(direction, chord_columns):
    result = 0
    while direction:
        low = direction & -direction
        result ^= chord_columns[low.bit_length() - 1]
        direction ^= low
    return result


def incident_comparison_witness(vertices, comparisons, *, method="auto"):
    """Decide arbitrary indexed pairs; integrate a witness on original wires."""
    edges = tuple(comparisons)
    if not isinstance(vertices, int) or vertices < 0 or len(edges) % 2:
        raise ValueError("expected nonnegative order and paired comparisons")
    for u, v, d in edges:
        if not (0 <= u < vertices and 0 <= v < vertices and d in (0, 1)):
            raise ValueError("invalid signed comparison")
    endpoints = [(u, v) for u, v, _ in edges]
    pairs = [(i, i + 1) for i in range(0, len(edges), 2)]
    if method not in ("auto", "dfs", "hull", "blockwise"):
        raise ValueError("expected auto, dfs, hull, or blockwise")
    if method != "blockwise" and any(
        set(endpoints[i]).isdisjoint(endpoints[j]) for i, j in pairs
    ):
        return total_comparison_witness(vertices, edges)
    backend = "hull" if method == "blockwise" else method
    seed = incident_directions(vertices, endpoints, pairs, method=backend)
    if not seed:
        return total_comparison_witness(vertices, edges)

    columns = _cycle_columns(vertices, edges)
    # For the provider's chord set Q the row bases satisfy H = H[:,Q] H_Q.
    # Transport its primal directions by the invertible matrix H[:,Q].
    chord_columns = [columns[i] for i in forest_chords(vertices, endpoints)]
    basis = _basis(_transport(h, chord_columns) for h in seed)
    target = 0
    for h, (_, _, d) in zip(columns, edges):
        if d:
            target ^= h
    shores = [((i,), (j,)) for i, j in pairs]
    flags = biclique_dual_witness([_reduce(h, basis) for h in columns],
                                  _reduce(target, basis), shores)
    if flags is None:
        return None
    # Honor quotient support when choosing one failure-eligible edge per pair.
    # G lies in the span of this orientation, so all complementary requests
    # can be satisfied simultaneously in the unquotiented graph.
    graph = [[] for _ in range(vertices)]
    for i, j in pairs:
        if flags[i] and flags[j]:
            raise AssertionError("illegal quotient flags")
        required = i if flags[j] else j
        u, v, d = edges[required]
        graph[u].append((v, d))
        graph[v].append((u, d))
    solution = _potentials(graph)
    if solution is None:
        raise AssertionError("certified oriented span failed to lift")
    values = solution[1]
    met = [values[u] ^ values[v] == d for u, v, d in edges]
    if not all(a or b for a, b in zip(met[::2], met[1::2])):
        raise AssertionError("original shell replay failed")
    return values


def incident_block_witness(shells, pins, *, method="auto"):
    """Decide physical matching shells and recover original signed copy bits."""
    if not isinstance(shells, int) or shells < 0:
        raise ValueError("expected a nonnegative shell count")
    n = 4 * shells
    pins = tuple(pins)
    graph = [[] for _ in range(n)]
    for a, b, d in pins:
        if not (0 <= a < n and 0 <= b < n and d in (0, 1)):
            raise ValueError("invalid signed pin")
        graph[a].append((b, d))
        graph[b].append((a, d))
    contracted = _potentials(graph)
    if contracted is None:
        return None
    roots, offsets = contracted
    edges = []
    for start in range(0, n, 4):
        for a in (start, start + 1):
            b = a + 2
            edges.append((roots[a], roots[b], 1 ^ offsets[a] ^ offsets[b]))
    values = incident_comparison_witness(n, edges, method=method)
    if values is None:
        return None
    raw = [values[r] ^ d for r, d in zip(roots, offsets)]
    if not all(raw[a] ^ raw[b] == d for a, b, d in pins):
        raise AssertionError("signed copy replay failed")
    if any(raw[a:a+2] == raw[a+2:a+4] for a in range(0, n, 4)):
        raise AssertionError("physical matching replay failed")
    return raw
