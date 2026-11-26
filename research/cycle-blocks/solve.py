"""Label witnesses for induced even-degree subgraphs of a simple graph."""
from itertools import combinations


def edge_blocks(adj):
    """Tarjan's biconnected edge partition, including bridge blocks."""
    seen = {}
    low = {}
    stack = []
    result = []

    def visit(u, parent):
        seen[u] = low[u] = len(seen)
        for v in adj[u]:
            if v not in seen:
                start = len(stack)
                stack.append((u, v))
                visit(v, u)
                low[u] = min(low[u], low[v])
                if low[v] >= seen[u]:
                    result.append(stack[start:])
                    del stack[start:]
            elif v != parent and seen[v] < seen[u]:
                stack.append((u, v))
                low[u] = min(low[u], seen[v])

    for u in range(len(adj)):
        if u not in seen:
            visit(u, None)
    return result


def even_edge_masks(edges):
    adj = {}
    for i, (u, v) in enumerate(edges):
        adj.setdefault(u, []).append((v, i))
        adj.setdefault(v, []).append((u, i))
    root = edges[0][0]
    path = {root: 0}
    queue = [root]
    tree = set()
    for u in queue:
        for v, i in adj[u]:
            if v not in path:
                path[v] = path[u] ^ (1 << i)
                tree.add(i)
                queue.append(v)
    masks = [0]
    for i, (u, v) in enumerate(edges):
        if i not in tree:
            cycle = path[u] ^ path[v] ^ (1 << i)
            masks += [x ^ cycle for x in masks]
    return masks


def join(left, right):
    """Disjoint subtree assignments with XOR labels and bit-mask witnesses."""
    return {x ^ y: s | t for x, s in left.items() for y, t in right.items()}


def solve(adj, labels, t):
    """Return one witness per attainable t-bit label, indexed by that label."""
    blocks = edge_blocks(adj)
    incidence = [[] for _ in adj]
    for j, edges in enumerate(blocks):
        for u in {v for edge in edges for v in edge}:
            incidence[u].append(j)
    visited = set()

    def vertex(u, parent):
        visited.add(u)
        result = [{0: 0}, {labels[u]: 1 << u}]
        for j in incidence[u]:
            if j != parent:
                child = block(j, u)
                result = [join(result[b], child[b]) for b in range(2)]
        return result

    def block(j, parent):
        edges = blocks[j]
        vertices = {v for edge in edges for v in edge}
        below = {u: vertex(u, j) for u in vertices - {parent}}
        answer = [{}, {}]
        for mask in even_edge_masks(edges):
            ends = {v for i, edge in enumerate(edges) if mask >> i & 1 for v in edge}
            for bit in (0, 1):
                if not bit and parent in ends:
                    continue
                fixed = ends | ({parent} if bit else set())
                if any(u in fixed and v in fixed and not (mask >> i & 1)
                       for i, (u, v) in enumerate(edges)):
                    continue
                optional = sorted(vertices - fixed - {parent})
                for size in range(min(t, len(optional)) + 1):
                    for extras in combinations(optional, size):
                        selected = fixed.union(extras)
                        if any(u in selected and v in selected and not (mask >> i & 1)
                               for i, (u, v) in enumerate(edges)):
                            continue
                        table = {0: 0}
                        for u, choices in below.items():
                            table = join(table, choices[int(u in selected)])
                        answer[bit].update(table)
        return answer

    answer = {0: 0}
    for root in range(len(adj)):
        if root not in visited:
            inactive, active = vertex(root, None)
            answer = join(answer, inactive | active)
    return answer
