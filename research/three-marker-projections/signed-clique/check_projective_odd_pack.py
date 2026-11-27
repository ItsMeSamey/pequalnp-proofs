"""Check the explicit transversal and exhaust odd simple cycles only at m=4."""
from itertools import combinations


def graph(m):
    crossing = {pair: i for i, pair in enumerate(combinations(range(1, m + 1), 2))}
    adj = [set() for _ in crossing]
    cover = {crossing[i, m+1-i] for i in range(1, m//2+1)}

    def add(u, v):
        adj[u].add(v)
        adj[v].add(u)

    for i in range(1, m+1):
        slopes = [j for j in range(1, m+1) if j != i]
        ids = [crossing[tuple(sorted((i, j)))] for j in slopes]
        for a, b, j in zip(ids, ids[1:], slopes):
            v = len(adj)
            adj.append(set())
            add(a, v)
            add(v, b)
            if 2*i == m+1 and j == i-1:
                cover.add(v)
        add(ids[-1], ids[0])
    return adj, cover


def bipartite(adj, deleted):
    colors = {}
    for v in range(len(adj)):
        if v in deleted or v in colors:
            continue
        colors[v] = 0
        stack = [v]
        while stack:
            x = stack.pop()
            for y in adj[x] - deleted:
                if y not in colors:
                    colors[y] = 1-colors[x]
                    stack.append(y)
                elif colors[y] == colors[x]:
                    return False
    return True


def odd_simple_cycles(adj):
    cycles = set()
    for start in range(len(adj)):
        stack = [(start, 1 << start)]
        while stack:
            u, mask = stack.pop()
            for v in adj[u]:
                if v == start and mask.bit_count() >= 3 and mask.bit_count() % 2:
                    cycles.add(mask)
                if v > start and not mask >> v & 1:
                    stack.append((v, mask | (1 << v)))
    return cycles


for m in range(4, 13):
    adj, cover = graph(m)
    assert len(adj) == m*(m-1)//2 + m*(m-2)
    assert sum(map(len, adj))//2 == m*(2*m-3)
    assert len(cover) == (m+1)//2 and bipartite(adj, cover)
    if m == 4:
        cycles = odd_simple_cycles(adj)
        assert cycles and all(a & b for a, b in combinations(cycles, 2))
        assert not any(bipartite(adj, {v}) for v in range(len(adj)))
print('nine explicit transversals passed; m=4 packing one and transversal two')
