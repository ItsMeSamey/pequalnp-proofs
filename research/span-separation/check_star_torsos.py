"""Verify the single-center connectivity implication and the four-port obstruction."""
from itertools import combinations, product
from random import Random


def partition(graph, color):
    parts = []
    remaining = set(range(len(graph)))
    while remaining:
        v = remaining.pop()
        block, queue = {v}, [v]
        while queue:
            u = queue.pop()
            nxt = {x for x in graph[u] & remaining if color[x] == color[u]}
            remaining -= nxt
            block |= nxt
            queue.extend(nxt)
        parts.append(block)
    return parts


def graph_from_edges(n, edges):
    graph = [set() for _ in range(n)]
    for a, b in edges:
        graph[a].add(b)
        graph[b].add(a)
    return graph


def check(rng):
    ports, inside = rng.randrange(1, 4), rng.randrange(1, 5)
    allports = set(range(ports))
    edges = [(ports + i, ports + rng.randrange(i)) for i in range(1, inside)]
    edges += [(v, ports + rng.randrange(inside)) for v in allports]
    edges += [(u, v) for u, v in combinations(range(ports + inside), 2)
              if v >= ports and rng.randrange(4) == 0]
    graph = graph_from_edges(ports + inside, edges)
    total = 0
    for colors in product(range(3), repeat=ports + inside):
        original = partition(graph, colors)
        if any(not (part & allports) for part in original):
            continue
        tally = [colors[:ports].count(c) for c in range(3)]
        normalized = colors[:ports] + (tally.index(max(tally)),) * inside
        after = partition(graph, normalized)
        for part in original:
            assert any(part & allports <= dest for dest in after)
        total += 1
    return total


if __name__ == "__main__":
    rng = Random(761)
    total = sum(check(rng) for _ in range(100))
    graph = graph_from_edges(6, [(0,4), (1,4), (4,5), (2,5), (3,5)])
    original = partition(graph, (0,0,1,1,0,1))
    assert len(original) == 2
    assert all(len(partition(graph, (0,0,1,1,c,c))) > 2 for c in (0,1))
    print(f"{total} local assignments preserved port connections; four-port obstruction verified")
