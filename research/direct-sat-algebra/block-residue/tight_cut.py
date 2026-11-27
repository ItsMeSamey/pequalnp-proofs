"""Deterministic nontrivial tight-cut finder for a connected matching-covered graph."""
from itertools import combinations


def tight_shore(vertices, edges, maximum_matching=None):
    """Return a nontrivial tight shore, or None for an indecomposable graph.

    vertices is an integer order or an iterable of hashable vertex IDs. Repeated
    endpoint pairs are allowed. The optional maximum_matching(V, E) returns an
    iterable of matched pairs in the indicated unweighted simple graph.
    """
    order = tuple(range(vertices) if isinstance(vertices, int) else vertices)
    adj = {v: set() for v in order}
    simple = []
    for x, y in edges:
        if x == y:
            raise ValueError("a matching-covered graph has no loops")
        if y not in adj[x]:
            simple.append((x, y))
            adj[x].add(y)
            adj[y].add(x)
    if len(order) < 6:
        return None
    if maximum_matching is None:
        from general_blossom import maximum_cardinality_matching as maximum_matching

    def matching(active):
        nodes = tuple(v for v in order if v in active)
        pairs = tuple((x, y) for x, y in simple if x in active and y in active)
        return list(maximum_matching(nodes, pairs))

    def components(active):
        unseen = set(active)
        for v in order:
            if v not in unseen:
                continue
            stack = [v]
            unseen.remove(v)
            component = {v}
            while stack:
                x = stack.pop()
                for y in adj[x] & unseen:
                    unseen.remove(y)
                    component.add(y)
                    stack.append(y)
            yield component

    all_nodes = set(order)
    color = {order[0]: 0}
    queue = [order[0]]
    for x in queue:
        for y in adj[x]:
            if y not in color:
                color[y] = color[x] ^ 1
                queue.append(y)
    if len(color) != len(order):
        raise ValueError("expected a connected matching-covered graph")
    bipartite = all(color[x] != color[y] for x, y in simple)
    if bipartite:
        left = [x for x in order if color[x] == 0]
        right = [x for x in order if color[x] == 1]
        for left_pair in combinations(left, 2):
            for right_pair in combinations(right, 2):
                active = all_nodes.difference(left_pair, right_pair)
                pairs = matching(active)
                if 2 * len(pairs) == len(active):
                    continue
                mate = dict(pairs + [(y, x) for x, y in pairs])
                reached = {x for x in left if x in active and x not in mate}
                queue = list(reached)
                for x in queue:
                    for y in adj[x] & active:
                        z = mate[y]  # An exposed right vertex would augment.
                        if z not in reached:
                            reached.add(z)
                            queue.append(z)
                neighbors = set().union(*(adj[x] for x in reached))
                return frozenset(reached | neighbors)
        return None

    for u, v in combinations(order, 2):
        active = all_nodes - {u, v}
        size = len(matching(active))
        if 2 * size != len(active):
            # D consists of all vertices left exposed by some maximum matching.
            exposed = {x for x in active if len(matching(active - {x})) == size}
            boundary = set().union(*(adj[x] for x in exposed)) & (active - exposed)
            for component in components(active - boundary):
                if len(component) >= 3 and len(component) % 2:
                    return frozenset(component)
            raise AssertionError("nonbipartite barrier has no nontrivial odd component")
        parts = list(components(active))
        if len(parts) > 1 and all(len(part) % 2 == 0 for part in parts):
            return frozenset(parts[0] | {u})
    return None
