"""Certificate of an induced long hole in a binary two-tag gain lift."""
from collections import deque


def long_hole(vertex_count, edges, bound):
    """Return a cycle of lift-vertex indices, or None. Parallel edges collapse."""
    if vertex_count < 0 or bound < 3:
        raise ValueError("vertex_count must be nonnegative and bound at least three")
    neighbors = [set() for _ in range(4 * vertex_count)]
    for u, v, tag in edges:
        if not (0 <= u < vertex_count and 0 <= v < vertex_count and 0 <= tag < 4):
            raise ValueError("invalid indexed edge")
        if u == v:
            continue
        for color in range(4):
            a, b = 4*u + color, 4*v + (color ^ tag)
            neighbors[a].add(b)
            neighbors[b].add(a)

    def search(path):
        if len(path) < bound:
            for vertex in neighbors[path[-1]]:
                if vertex not in path and all(vertex not in neighbors[p] for p in path[:-1]):
                    answer = search(path + [vertex])
                    if answer is not None:
                        return answer
            return None
        interior = set(path[1:-1])
        blocked = interior.union(*(neighbors[p] for p in interior))
        start, end = path[0], path[-1]
        blocked.difference_update((start, end))
        queue = deque([start])
        previous = {start: None}
        while queue:
            p = queue.popleft()
            for v in neighbors[p] - blocked:
                if v in previous:
                    continue
                previous[v] = p
                if v == end:
                    back = []
                    while p != start:
                        back.append(p)
                        p = previous[p]
                    return path + back
                queue.append(v)
        return None

    for start in range(len(neighbors)):
        found = search([start])
        if found is not None:
            return found
    return None
