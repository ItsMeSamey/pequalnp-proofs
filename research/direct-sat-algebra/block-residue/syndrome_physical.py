"""Original indexed comparisons and signed copy pins via quotient syndrome DP."""

from balanced_block import _potentials
from biclique_period import _basis, _reduce
from biclique_physical import _cycle_columns
from incident_port import forest_chords, incident_directions
from incident_total import _transport
from syndrome_dp import syndrome_witness


def syndrome_comparison_witness(vertices, comparisons, *, method="auto", guarantee="auto",
                                max_dp_bytes=None):
    """Solve arbitrary consecutive indexed pairs, returning original vertex bits."""
    edges = tuple(comparisons)
    if not isinstance(vertices, int) or vertices < 0 or len(edges) % 2:
        raise ValueError("expected nonnegative order and paired comparisons")
    for x, y, d in edges:
        if not (0 <= x < vertices and 0 <= y < vertices and d in (0, 1)):
            raise ValueError("invalid comparison")
    if guarantee not in ("auto", "dfs", "hull", "blockwise"):
        raise ValueError("invalid guarantee method")
    if method not in ("auto", "dp", "orientation"):
        raise ValueError("invalid syndrome method")
    endpoints = [(x, y) for x, y, _ in edges]
    pairs = [(i, i + 1) for i in range(0, len(edges), 2)]
    columns = _cycle_columns(vertices, edges)
    basis = {}
    if guarantee == "blockwise" or all(
        not set(endpoints[i]).isdisjoint(endpoints[j]) for i, j in pairs
    ):
        backend = "hull" if guarantee == "blockwise" else guarantee
        seed = incident_directions(vertices, endpoints, pairs, method=backend)
        chord_columns = [columns[k] for k in forest_chords(vertices, endpoints)]
        basis = _basis(_transport(h, chord_columns) for h in seed)

    target = 0
    for h, (_, _, d) in zip(columns, edges):
        if d:
            target ^= h
    shores = [((i,), (j,)) for i, j in pairs]
    flags = syndrome_witness([_reduce(h, basis) for h in columns],
                             _reduce(target, basis), shores, method=method,
                             max_dp_bytes=max_dp_bytes)
    if flags is None:
        return None

    # Quotient flags choose eligible failure edges, not necessarily actual failures.
    # Solve complementary requests on original vertices to lift the orientation.
    graph = [[] for _ in range(vertices)]
    for i, j in pairs:
        if flags[i] and flags[j]:
            raise AssertionError("invalid quotient orientation")
        x, y, d = edges[i if flags[j] else j]
        graph[x].append((y, d))
        graph[y].append((x, d))
    lifted = _potentials(graph)
    if lifted is None:
        raise AssertionError("quotient orientation has no original lift")
    values = lifted[1]
    good = [values[x] ^ values[y] == d for x, y, d in edges]
    if not all(good[i] or good[j] for i, j in pairs):
        raise AssertionError("original shell replay failed")
    return values


def syndrome_block_witness(shells, pins, *, method="auto", guarantee="auto",
                           max_dp_bytes=None):
    """Solve physical four-bit shells, preserving original signed copy offsets."""
    if not isinstance(shells, int) or shells < 0:
        raise ValueError("expected a nonnegative shell count")
    n = 4 * shells
    graph = [[] for _ in range(n)]
    pins = tuple(pins)
    for a, b, d in pins:
        if not (0 <= a < n and 0 <= b < n and d in (0, 1)):
            raise ValueError("invalid signed pin")
        graph[a].append((b, d))
        graph[b].append((a, d))
    quotient = _potentials(graph)
    if quotient is None:
        return None
    roots, offsets = quotient
    edges = []
    for start in range(0, n, 4):
        for a in (start, start + 1):
            b = a + 2
            edges.append((roots[a], roots[b], 1 ^ offsets[a] ^ offsets[b]))
    values = syndrome_comparison_witness(n, edges, method=method, guarantee=guarantee,
                                        max_dp_bytes=max_dp_bytes)
    if values is None:
        return None
    raw = [values[root] ^ d for root, d in zip(roots, offsets)]
    if not all(raw[a] ^ raw[b] == d for a, b, d in pins):
        raise AssertionError("original pin replay failed")
    if any(raw[a:a + 2] == raw[a + 2:a + 4] for a in range(0, n, 4)):
        raise AssertionError("original color replay failed")
    return raw
