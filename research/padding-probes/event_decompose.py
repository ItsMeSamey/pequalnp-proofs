"""Recognize partial 2-trees, optionally after deleting one vertex."""
from collections import deque


def decompose(vertices, edges):
    """Return bags and tree_edges, or unknown outside the recognized class.

    Vertex IDs are arbitrary hashable objects. A loop needs only a vertex bag.
    The empty graph gets one empty bag of width -1.
    """
    vertices = tuple(dict.fromkeys(vertices))
    ids = {v: i for i, v in enumerate(vertices)}
    graph = [set() for _ in vertices]
    for u, v in edges:
        if u not in ids or v not in ids:
            raise ValueError('edge endpoint absent from vertex set')
        i, j = ids[u], ids[v]
        if i != j:
            graph[i].add(j)
            graph[j].add(i)
    attempts = 0
    for apex in range(-1, len(vertices)):
        attempts += 1
        adjacency = {i: neighbors - {apex} for i, neighbors in enumerate(graph) if i != apex}
        ready = deque(i for i, neighbors in adjacency.items() if len(neighbors) <= 2)
        removed = []
        while ready:
            i = ready.popleft()
            if i not in adjacency:
                continue
            neighbors = tuple(adjacency.pop(i))
            removed.append((i, neighbors))
            for j in neighbors:
                adjacency[j].remove(i)
            if len(neighbors) == 2:
                u, v = neighbors
                adjacency[u].add(v)
                adjacency[v].add(u)
            for j in neighbors:
                if len(adjacency[j]) <= 2:
                    ready.append(j)
        if adjacency:
            continue
        order = {v: i for i, (v, _) in enumerate(removed)}
        bags = []
        links = []
        roots = []
        for i, (v, neighbors) in enumerate(removed):
            bag = [vertices[v], *(vertices[j] for j in neighbors)]
            if apex >= 0:
                bag.append(vertices[apex])
            bags.append(tuple(bag))
            if neighbors:
                links.append((i, min(order[j] for j in neighbors)))
            else:
                roots.append(i)
        links.extend(zip(roots, roots[1:]))
        if not bags:
            bags = [() if apex == -1 else (vertices[apex],)]
        return dict(status='ok', bags=bags, tree_edges=links, attempts=attempts,
                    apex=None if apex == -1 else vertices[apex],
                    width=max(map(len, bags)) - 1)
    return dict(status='unknown', attempts=attempts, reason='outside apex partial 2-tree class')
