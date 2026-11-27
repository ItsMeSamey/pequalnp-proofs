"""Width-three decompositions from biconnected blocks with individual apexes."""
from event_decompose import decompose as _local


def _blocks(graph):
    """Iterative undirected lowlink DFS; yield component root and block edges."""
    depth = [-1] * len(graph)
    low = [0] * len(graph)
    parent = [-1] * len(graph)
    pending = []
    clock = 0
    for root in range(len(graph)):
        if depth[root] != -1:
            continue
        depth[root] = low[root] = clock
        clock += 1
        if not graph[root]:
            yield root, (root,), ()
            continue
        frames = [(root, iter(graph[root]))]
        while frames:
            u, neighbors = frames[-1]
            v = next(neighbors, None)
            if v is not None:
                if depth[v] == -1:
                    parent[v] = u
                    pending.append((u, v))
                    depth[v] = low[v] = clock
                    clock += 1
                    frames.append((v, iter(graph[v])))
                elif v != parent[u] and depth[v] < depth[u]:
                    low[u] = min(low[u], depth[v])
                    pending.append((u, v))
                continue
            frames.pop()
            p = parent[u]
            if p == -1:
                continue
            low[p] = min(low[p], low[u])
            if low[u] >= depth[p]:
                block = []
                while True:
                    edge = pending.pop()
                    block.append(edge)
                    if edge == (p, u):
                        break
                yield root, {v for edge in block for v in edge}, block


def decompose(vertices, edges):
    """Glue certified local bags along articulation vertices and component roots."""
    names = tuple(dict.fromkeys(vertices))
    indices = {name: i for i, name in enumerate(names)}
    graph = [set() for _ in names]
    for a, b in edges:
        if a not in indices or b not in indices:
            raise ValueError('edge endpoint absent from vertex set')
        u, v = indices[a], indices[b]
        if u != v:
            graph[u].add(v)
            graph[v].add(u)
    bags = []
    tree_edges = []
    components = {}
    anchors = {}
    attempts = block_count = 0
    apexes = []
    for root, vertices_in_block, edges_in_block in _blocks(graph):
        block_count += 1
        local = _local(vertices_in_block, edges_in_block)
        attempts += local['attempts']
        if local['status'] != 'ok':
            return dict(status='unknown', reason='unrecognized biconnected block',
                        attempts=attempts, blocks=block_count)
        apex = local['apex']
        if apex is not None:
            apexes.append(names[apex])
        offset = len(bags)
        components.setdefault(root, offset)
        first = {}
        for i, bag in enumerate(local['bags'], offset):
            bags.append(tuple(names[u] for u in bag))
            for u in bag:
                first.setdefault(u, i)
        tree_edges.extend((offset + i, offset + j) for i, j in local['tree_edges'])
        for u, i in first.items():
            if u in anchors:
                tree_edges.append((anchors[u], i))
            else:
                anchors[u] = i
    roots = list(components.values())
    tree_edges.extend(zip(roots, roots[1:]))
    if not bags:
        bags = [()]
    return dict(status='ok', bags=bags, tree_edges=tree_edges,
                width=max(map(len, bags)) - 1, blocks=block_count,
                attempts=attempts, apexes=apexes)
