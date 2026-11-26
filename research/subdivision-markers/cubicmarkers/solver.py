"""Deterministic parity-marker solver on graphs with no edge joining two vertices of degree >2."""
from itertools import combinations


def cycle_basis(neighbors, forbidden):
    """Return fundamental cycles as edge masks, with vertex incidence masks."""
    n = len(neighbors)
    parent = {}
    tree_edges = set()
    paths = [0] * n
    incident = [0] * n
    edges = [(i, j) for i, row in enumerate(neighbors) for j in row if i < j
             and not forbidden >> i & 1 and not forbidden >> j & 1]
    indices = {}
    for k, (i, j) in enumerate(edges):
        indices[i, j] = indices[j, i] = k
        incident[i] |= 1 << k
        incident[j] |= 1 << k
    for root in range(n):
        if root in parent or forbidden >> root & 1:
            continue
        parent[root] = None
        stack = [root]
        while stack:
            i = stack.pop()
            for j in neighbors[i]:
                if j in parent or forbidden >> j & 1:
                    continue
                parent[j] = i
                k = indices[i, j]
                tree_edges.add(k)
                paths[j] = paths[i] ^ (1 << k)
                stack.append(j)
    basis = [paths[i] ^ paths[j] ^ (1 << k)
             for k, (i, j) in enumerate(edges) if k not in tree_edges]
    return basis, incident


def solve(neighbors, labels, target, markers):
    """Return a vertex mask or None. Rows are neighbor lists of a simple undirected graph."""
    n = len(neighbors)
    if len(labels) != n or any(w < 0 or w >= 1 << markers for w in [*labels, target]):
        raise ValueError('Label dimension mismatch')
    rows = [set(row) for row in neighbors]
    if any(i in row or any(j < 0 or j >= n or i not in rows[j] for j in row)
           or len(row) != len(neighbors[i]) for i, row in enumerate(rows)):
        raise ValueError('Expected a simple undirected graph')
    if any(len(row) > 2 and any(len(rows[j]) > 2 for j in row) for row in rows):
        raise ValueError('An edge joins two vertices of degree above two')
    near = [sum(1 << j for j in row) for row in rows]
    choices = [i for i, label in enumerate(labels) if label]
    for size in range(min(len(choices), markers) + 1):
        for isolates in combinations(choices, size):
            support = sum(1 << i for i in isolates)
            if any(near[i] & support for i in isolates):
                continue
            forbidden = support
            needed = target
            for i in isolates:
                forbidden |= near[i]
                needed ^= labels[i]
            if needed == 0:
                return support
            basis, incident = cycle_basis(rows, forbidden)
            degree = max((m.bit_count() - 1 for m in incident if m), default=0)
            for weight in range(1, min(len(basis), markers * degree) + 1):
                for terms in combinations(basis, weight):
                    edges = 0
                    for term in terms:
                        edges ^= term
                    value = 0
                    selected = support
                    for i, mask in enumerate(incident):
                        if mask & edges:
                            selected |= 1 << i
                            value ^= labels[i]
                    if value == needed:
                        return selected
    return None
