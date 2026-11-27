"""Propose, without certifying, partitions of a simple undirected graph."""
from itertools import combinations


def proposals(vertices, edges):
    """Yield threshold component partitions, indexed by original vertex labels."""
    vertices = tuple(vertices)
    index = {v: i for i, v in enumerate(vertices)}
    if len(index) != len(vertices):
        raise ValueError("duplicate vertex")
    adjacency = [0] * len(vertices)
    for u, v in edges:
        i, j = index[u], index[v]
        if i == j:
            raise ValueError("loop")
        adjacency[i] |= 1 << j
        adjacency[j] |= 1 << i
    buckets = {}
    for i, j in combinations(range(len(vertices)), 2):
        common = (adjacency[i] & adjacency[j]).bit_count()
        buckets.setdefault(common, []).append((i, j))
    parent = list(range(len(vertices)))

    def root(i):
        while i != parent[i]:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    yield tuple((v,) for v in vertices)
    for threshold in sorted(buckets, reverse=True):
        changed = False
        for i, j in buckets[threshold]:
            left, right = root(i), root(j)
            if left != right:
                parent[right] = left
                changed = True
        if changed:
            groups = {}
            for i, v in enumerate(vertices):
                groups.setdefault(root(i), []).append(v)
            yield tuple(tuple(bag) for bag in groups.values())
