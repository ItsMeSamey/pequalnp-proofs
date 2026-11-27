"""Produce a labeled graph witness and independently check a named three-spoke star."""
from operator import index
import subprocess


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


def make_graph(columns, executable):
    """Return original-order edges or None for a CMR negative verdict.

    Forest rows are r1,...,rr and nonforest columns are c1,...,ck.
    Duplicate supports restore parallel edges, and zero supports restore loops.
    CMR resource failures and malformed positive answers raise exceptions.
    """
    columns = tuple(columns)
    rank, coordinates = _coordinates(columns)
    supports = sorted({c for c in coordinates if c.bit_count() > 1})
    if not supports:
        edges = {1 << i: (0, i + 1) for i in range(rank)}
        return [edges[c] if c else (0, 0) for c in coordinates]
    rows = [" ".join(str((column >> row) & 1) for column in supports)
            for row in range(rank)]
    matrix = "\n".join([f"{rank} {len(supports)}", *rows, ""])
    result = subprocess.run(
        ["prlimit", "--as=268435456", "--",
         executable, "-", "-i", "dense", "-G", "-"],
        input=matrix, capture_output=True, text=True, timeout=30, check=True)
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
        original = [edges[c] if c else (0, 0) for c in coordinates]
        if not _same_kernel(columns, original):
            raise ValueError("CMR output has a different labeled kernel")
        return original
    return None


def _rank(columns):
    pivots = {}
    for value in columns:
        while value:
            bit = value.bit_length()
            if bit not in pivots:
                pivots[bit] = value
                break
            value ^= pivots[bit]
    return len(pivots)


def _same_kernel(columns, edges):
    if len(columns) != len(edges):
        return False
    if any(type(c) is not int or c < 0 for c in columns):
        return False
    vertex_ids = {}
    incidence = []
    for u, v in edges:
        if type(u) is not int or type(v) is not int or min(u, v) < 0:
            return False
        i = vertex_ids.setdefault(u, len(vertex_ids))
        j = vertex_ids.setdefault(v, len(vertex_ids))
        incidence.append((1 << i) ^ (1 << j))
    shift = max((c.bit_length() for c in columns), default=0)
    stacked = (a | (b << shift) for a, b in zip(columns, incidence))
    # The stacked kernel is the intersection. Equal dimensions prove equality.
    return _rank(columns) == _rank(incidence) == _rank(stacked)


def check_star(columns, edges, root_positions=(0, 1, 2)):
    """Verify equal labeled kernels and a common center with three distinct leaves."""
    try:
        columns, edges, roots = tuple(columns), tuple(map(tuple, edges)), tuple(root_positions)
        if len(roots) != 3 or any(type(i) is not int or i < 0 or i >= len(edges) for i in roots):
            return False
        if len(set(roots)) != 3 or not _same_kernel(columns, edges):
            return False
        spokes = [set(edges[i]) for i in roots]
        return (all(len(edge) == 2 for edge in spokes)
                and len(set.intersection(*spokes)) == 1
                and len(set.union(*spokes)) == 4)
    except (TypeError, ValueError):
        return False
