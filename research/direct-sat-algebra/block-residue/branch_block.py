"""Decision and witness recovery by identifying branch vertices in signed blocks."""

from balanced_block import _potentials, comparison_witness


def _blocks(graph):
    """Yield edge-ID blocks by iterative low-link DFS, including singleton loops."""
    n = len(graph)
    seen = [-1] * n
    low = [0] * n
    incoming = [-1] * n
    clock = 0
    pending = []
    for root in range(n):
        if seen[root] >= 0:
            continue
        seen[root] = low[root] = clock
        clock += 1
        todo = [(root, iter(graph[root]))]
        while todo:
            x, neighbors = todo[-1]
            item = next(neighbors, None)
            if item is None:
                todo.pop()
                if todo:
                    p = todo[-1][0]
                    low[p] = min(low[p], low[x])
                    if low[x] >= seen[p]:
                        block = []
                        while True:
                            e = pending.pop()
                            block.append(e)
                            if e == incoming[x]:
                                break
                        yield block
                continue
            y, e = item
            if e == incoming[x]:
                continue
            if y == x:
                yield [e]
            elif seen[y] < 0:
                pending.append(e)
                incoming[y] = e
                seen[y] = low[y] = clock
                clock += 1
                todo.append((y, iter(graph[y])))
            elif seen[y] < seen[x]:
                pending.append(e)
                low[x] = min(low[x], seen[y])


def _stars(vertices, edges):
    graph = [[] for _ in range(vertices)]
    for e, (x, y, d) in enumerate(edges):
        if not (0 <= x < vertices and 0 <= y < vertices and d in (0, 1)):
            raise ValueError("invalid comparison")
        graph[x].append((y, e))
        if x != y:
            graph[y].append((x, e))
    stars = []
    for block in _blocks(graph):
        if len(block) <= 2:
            continue
        adjacency = {}
        for e in block:
            x, y, d = edges[e]
            adjacency.setdefault(x, []).append((y, d))
            adjacency.setdefault(y, []).append((x, d))
        high = [x for x, neighbors in adjacency.items() if len(neighbors) >= 3]
        if not high:
            continue
        values = {high[0]: 0}
        stack = [high[0]]
        balanced = True
        while stack and balanced:
            x = stack.pop()
            for y, d in adjacency[x]:
                required = values[x] ^ d
                if y not in values:
                    values[y] = required
                    stack.append(y)
                elif values[y] != required:
                    balanced = False
                    break
        if not balanced:
            stars.extend((high[0], x) for x in high[1:])
    return stars


def branch_comparison_witness(vertices, comparisons):
    """Return original vertex bits or None. Consecutive edge pairs form shells."""
    edges = list(comparisons)
    if not isinstance(vertices, int) or vertices < 0 or len(edges) % 2:
        raise ValueError("expected nonnegative order and paired comparisons")
    stars = _stars(vertices, edges)
    for branch in range(1 << len(stars)):
        equations = [[] for _ in range(vertices)]
        for i, (x, y) in enumerate(stars):
            d = (branch >> i) & 1
            equations[x].append((y, d))
            equations[y].append((x, d))
        components = _potentials(equations)
        if components is None:
            raise AssertionError("branch equations must form a forest")
        roots, offsets = components
        rewritten = [(roots[x], roots[y], d ^ offsets[x] ^ offsets[y])
                     for x, y, d in edges]
        values = comparison_witness(vertices, rewritten)
        if values is not None:
            return [values[root] ^ off for root, off in zip(roots, offsets)]
    return None


def branch_block_witness(shells, pins):
    """Solve four-bit matching shells with original signed raw-coordinate pins."""
    if not isinstance(shells, int) or shells < 0:
        raise ValueError("expected nonnegative shell count")
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
    values = branch_comparison_witness(n, comparisons)
    if values is None:
        return None
    return [values[root] ^ off for root, off in zip(roots, offsets)]
