"""Exact finite graphic recognition for labeled binary columns.

The fallback enumerates (r+1)^(r-1) trees at rank r, times polynomial
work per tree. It is not a polynomial-time implementation.
"""

from heapq import heapify, heappop, heappush
from itertools import product
from operator import index


def _coordinates(columns):
    pivots = {}
    coordinates = []
    for column in columns:
        remainder = index(column)
        if remainder < 0:
            raise ValueError("binary column bitmasks must be nonnegative")
        support = 0
        while remainder:
            pivot = remainder.bit_length() - 1
            if pivot not in pivots:
                # The original column becomes the next basis element.
                unit = 1 << len(pivots)
                pivots[pivot] = remainder, support ^ unit
                support = unit
                break
            vector, combination = pivots[pivot]
            remainder ^= vector
            support ^= combination
        coordinates.append(support)
    return len(pivots), coordinates


def _fundamental_supports(columns):
    rank, coordinates = _coordinates(columns)
    return rank, {c for c in coordinates if c.bit_count() > 1}


def _root_paths(word, size):
    """Decode a Prüfer word. Edge i is the parent edge of vertex i+1."""
    degree = [1] * size
    for vertex in word:
        degree[vertex] += 1
    leaves = [vertex for vertex in range(size) if degree[vertex] == 1]
    heapify(leaves)
    neighbors = [[] for _ in degree]
    for vertex in word:
        leaf = heappop(leaves)
        neighbors[leaf].append(vertex)
        neighbors[vertex].append(leaf)
        degree[vertex] -= 1
        if degree[vertex] == 1:
            heappush(leaves, vertex)
    u, v = leaves
    neighbors[u].append(v)
    neighbors[v].append(u)
    paths = [0] * size
    stack = [(0, -1)]
    while stack:
        vertex, parent = stack.pop()
        for child in neighbors[vertex]:
            if child != parent:
                paths[child] = paths[vertex] ^ (1 << (child - 1))
                stack.append((child, vertex))
    return paths


def is_graphic(columns):
    """Decide whether nonnegative integer columns represent a cycle matroid.

    In a graphic realization the selected basis is a spanning forest. Glue
    one vertex from each component to make it a tree without changing any
    circuit. Root the tree and name each nonroot vertex by its incoming
    basis edge. This vertex labeling occurs among the enumerated trees.
    Every nonbasis column then gives the unique tree path between its
    endpoints in basis coordinates. Conversely, a simultaneous path
    realization constructs a graph by adding the corresponding edges.
    Empty paths give loops and duplicate paths give parallel edges.
    """
    rank, supports = _fundamental_supports(columns)
    if not supports:
        return True
    if len(supports) + rank > rank * (rank + 1) // 2:
        return False
    size = rank + 1
    for word in product(range(size), repeat=rank - 1):
        paths = set(_root_paths(word, size))
        if all(any((path ^ support) in paths for path in paths)
               for support in supports):
            return True
    return False


def is_graphic_cmr(columns, executable="cmr-graphic", timeout=30, memory_mib=256):
    """Recognize graphicness using an installed CMR executable on Linux.

    In basis coordinates the representation is [I | A]. Removing loops and
    redundant parallel copies preserves graphicness in both directions
    (add a loop or a parallel graph edge to restore each removed element).
    Thus the distinct nonsingleton supports returned by the basis reduction
    give all columns of the simplified A. CMR expects its rows to be the
    forest edges and its columns to be the coforest edges, exactly as here.
    Upstream contract: https://discopt.github.io/cmr/graphic_8c.html
    CLI: https://github.com/discopt/cmr/blob/main/src/main/graphic_main.c
    Format: https://discopt.github.io/cmr/file-formats.html

    Resource exhaustion, missing tools, and unknown output raise exceptions.
    """
    import subprocess

    rank, coordinates = _coordinates(columns)
    supports = sorted({c for c in coordinates if c.bit_count() > 1})
    if not supports:
        edges = {1 << i: (i, i + 1) for i in range(rank)}
        _verify_labeled_graph(coordinates, edges)
        return True
    rows = [" ".join(str((column >> row) & 1) for column in supports)
            for row in range(rank)]
    matrix = "\n".join([f"{rank} {len(supports)}", *rows, ""])
    result = subprocess.run(
        ["prlimit", f"--as={memory_mib * 1024 * 1024}", "--",
         executable, "-", "-i", "dense", "-G", "-"],
        input=matrix, capture_output=True, text=True, timeout=timeout, check=True)
    verdicts = {"Matrix IS graphic.": True, "Matrix is NOT graphic.": False}
    parsed = [verdicts[line] for line in result.stderr.splitlines()
              if line in verdicts]
    if len(parsed) != 1:
        raise RuntimeError("CMR returned no unique graphicness verdict")
    if parsed[0]:
        labels = {f"r{i+1}": 1 << i for i in range(rank)}
        labels.update({f"c{i+1}": c for i, c in enumerate(supports)})
        edges = {}
        for line in result.stdout.splitlines():
            u, v, label = line.split()
            if label not in labels:
                raise ValueError("unknown or duplicate CMR graph label")
            edges[labels.pop(label)] = int(u), int(v)
        if labels:
            raise ValueError("missing CMR graph labels")
        _verify_labeled_graph(coordinates, edges)
    return parsed[0]


def _verify_labeled_graph(coordinates, edges):
    """Equal greedy coordinates iff both column maps have the same kernel.

    At each position the greedy basis grows exactly for an independent
    column. A dependent column gives its unique relation to earlier basis
    positions. Those relations, one per dependent position, form a kernel
    basis by their distinct leading positions. Thus equality checks both
    kernel inclusions in polynomial time, including loops and duplicates.
    """
    vertices = {}
    incidence = []
    for support in coordinates:
        u, v = edges[support] if support else (0, 0)
        i = vertices.setdefault(u, len(vertices))
        j = vertices.setdefault(v, len(vertices))
        incidence.append((1 << i) ^ (1 << j))
    if _coordinates(incidence)[1] != coordinates:
        raise ValueError("CMR graph and input have different labeled cycle kernels")
