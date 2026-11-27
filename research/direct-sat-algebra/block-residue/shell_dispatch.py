"""Polynomial-space dimension/codimension dispatch for original indexed shells."""

from pathlib import Path
import sys

from balanced_block import _potentials
from fourier_physical import comparison_count_witness


def choose_backend(d, r):
    """Select by exact comparison of (3/2)**d and 2**r, ties to affine."""
    if not all(isinstance(v, int) and v >= 0 for v in (d, r)):
        raise ValueError("expected nonnegative dimensions")
    return "affine" if 3**d <= 1 << (d + r) else "fourier"


def _archive_solve():
    # On the shared source tree the archive lives in scratch/compression.
    # Isolated releases may instead put its three unchanged modules on sys.path.
    try:
        from affine_cover_solver import solve
    except ModuleNotFoundError as exc:
        if exc.name != "affine_cover_solver":
            raise
        archive = Path(__file__).resolve().parents[2] / "compression"
        sys.path.insert(0, str(archive))
        try:
            from affine_cover_solver import solve
        finally:
            sys.path.pop(0)
    return solve


def dispatch_comparison_witness(vertices, comparisons, *, method="auto"):
    """Return original vertex bits, or None. Consecutive comparisons form shells."""
    if not isinstance(vertices, int) or vertices < 0 or method not in ("auto", "affine", "fourier"):
        raise ValueError("invalid order or method")
    edges = tuple(comparisons)
    if len(edges) % 2:
        raise ValueError("expected paired comparisons")
    graph = [[] for _ in range(vertices)]
    for x, y, sign in edges:
        if not (0 <= x < vertices and 0 <= y < vertices and sign in (0, 1)):
            raise ValueError("invalid signed comparison")
        graph[x].append((y, 0))
        graph[y].append((x, 0))
    roots, _ = _potentials(graph)
    # Fixing one root to zero per connected component preserves every difference.
    masks = [0] * vertices
    d = 0
    for x, root in enumerate(roots):
        if x != root:
            masks[x] = 1 << d
            d += 1
    r = len(edges) - d
    if method == "auto":
        method = choose_backend(d, r)
    if method == "fourier":
        return comparison_count_witness(vertices, edges)[1]
    # A shell fails iff both requested differences take their opposite values.
    rows = [(masks[x] ^ masks[y], sign ^ 1) for x, y, sign in edges]
    flats = list(zip(rows[::2], rows[1::2]))
    point = _archive_solve()(d, flats, kernels=False, separator=False)
    if point is None:
        return None
    bits = [int(bool(point & mask)) for mask in masks]
    ok = [bits[x] ^ bits[y] == sign for x, y, sign in edges]
    if not all(a or b for a, b in zip(ok[::2], ok[1::2])):
        raise AssertionError("affine lift failed original shell replay")
    return bits


def dispatch_block_witness(shells, pins, *, method="auto"):
    """Recover original four-bit shell assignments subject to signed copy pins."""
    if not isinstance(shells, int) or shells < 0 or method not in ("auto", "affine", "fourier"):
        raise ValueError("invalid shell count or method")
    n = 4 * shells
    pins = tuple(pins)
    graph = [[] for _ in range(n)]
    for a, b, sign in pins:
        if not (0 <= a < n and 0 <= b < n and sign in (0, 1)):
            raise ValueError("invalid signed pin")
        graph[a].append((b, sign))
        graph[b].append((a, sign))
    solution = _potentials(graph)
    if solution is None:
        return None
    roots, offsets = solution
    names = {root: i for i, root in enumerate(dict.fromkeys(roots))}
    ids = [names[root] for root in roots]
    edges = []
    for start in range(0, n, 4):
        for a in (start, start + 1):
            b = a + 2
            edges.append((ids[a], ids[b], 1 ^ offsets[a] ^ offsets[b]))
    bits = dispatch_comparison_witness(len(names), edges, method=method)
    if bits is None:
        return None
    raw = [bits[i] ^ off for i, off in zip(ids, offsets)]
    if not all(raw[a] ^ raw[b] == sign for a, b, sign in pins):
        raise AssertionError("signed copy replay failed")
    if any(raw[a:a+2] == raw[a+2:a+4] for a in range(0, n, 4)):
        raise AssertionError("original color shell replay failed")
    return raw
