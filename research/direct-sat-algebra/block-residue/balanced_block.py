"""Signed comparison blocks that are balanced or simple cycles."""

from cactus_copy import _repair


class UnsupportedBlock(ValueError):
    """An unbalanced block has cycle rank greater than one."""


def _potentials(graph):
    """Solve signed differences, retaining component roots and offsets."""
    roots = [-1] * len(graph)
    values = [0] * len(graph)
    for root in range(len(graph)):
        if roots[root] != -1:
            continue
        roots[root] = root
        stack = [root]
        while stack:
            x = stack.pop()
            for y, difference in graph[x]:
                required = values[x] ^ difference
                if roots[y] == -1:
                    roots[y] = root
                    values[y] = required
                    stack.append(y)
                elif values[y] != required:
                    return None
    return roots, values


def comparison_witness(vertices, comparisons):
    """Solve paired edges (x,y,d), where meeting either difference d suffices.

    Consecutive pairs form shells. Return vertex potentials or None. Reject
    unbalanced nonsimple blocks with UnsupportedBlock.
    """
    edges = list(comparisons)
    if vertices < 0 or len(edges) % 2:
        raise ValueError("expected nonnegative order and paired comparisons")
    graph = [[] for _ in range(vertices)]
    for e, (x, y, d) in enumerate(edges):
        if not (0 <= x < vertices and 0 <= y < vertices and d in (0, 1)):
            raise ValueError("invalid comparison")
        graph[x].append((y, e))
        graph[y].append((x, e))
    parent = [-1] * vertices
    depth = [0] * vertices
    incoming = [-1] * vertices
    tree = set()
    for root in range(vertices):
        if parent[root] != -1:
            continue
        parent[root] = root
        stack = [root]
        while stack:
            x = stack.pop()
            for y, e in graph[x]:
                if parent[y] == -1:
                    parent[y] = x
                    depth[y] = depth[x] + 1
                    incoming[y] = e
                    tree.add(e)
                    stack.append(y)
    uses = [0] * len(edges)
    violated = []
    for e, (x, y, parity) in enumerate(edges):
        if e in tree:
            continue
        cycle = [e]
        while x != y:
            if depth[x] < depth[y]:
                x, y = y, x
            step = incoming[x]
            uses[step] += 1
            parity ^= edges[step][2]
            cycle.append(step)
            x = parent[x]
        if parity:
            violated.append(cycle)

    # Sharing a tree edge connects two fundamental cycles in the same
    # cycle-matroid component. An isolated fundamental cycle is a whole block.
    if any(uses[e] > 1 for cycle in violated for e in cycle):
        raise UnsupportedBlock("unbalanced block has overlapping cycles")
    flipped = _repair(violated)
    if flipped is None:
        return None
    signed = [[] for _ in range(vertices)]
    for e, (x, y, d) in enumerate(edges):
        difference = d ^ (e in flipped)
        signed[x].append((y, difference))
        signed[y].append((x, difference))
    solution = _potentials(signed)
    if solution is None:
        raise AssertionError("repaired original comparisons must lift")
    return solution[1]


def balanced_block_witness(shells, pins):
    """Return original raw bits for signed pin triples and four-bit shells."""
    if not isinstance(shells, int) or shells < 0:
        raise ValueError("expected a nonnegative shell count")
    n = 4 * shells
    graph = [[] for _ in range(n)]
    for a, b, sign in pins:
        if not (0 <= a < n and 0 <= b < n and sign in (0, 1)):
            raise ValueError("invalid signed pin")
        graph[a].append((b, sign))
        graph[b].append((a, sign))
    contracted = _potentials(graph)
    if contracted is None:
        return None
    roots, offsets = contracted
    comparisons = []
    for shell in range(shells):
        for position in (0, 1):
            a = 4 * shell + position
            b = a + 2
            comparisons.append((roots[a], roots[b], 1 ^ offsets[a] ^ offsets[b]))
    values = comparison_witness(n, comparisons)
    if values is None:
        return None
    return [values[root] ^ off for root, off in zip(roots, offsets)]
