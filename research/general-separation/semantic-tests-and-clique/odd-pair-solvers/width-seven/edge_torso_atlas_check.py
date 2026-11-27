"""Check full-word minimality at each marked edge of the connected graph atlas."""
from collections import Counter
import networkx as nx


def witnesses(rows, a, b):
    pins = (1 << a) | (1 << b)
    full = (1 << len(rows)) - 1
    target = sum((r.bit_count() % 2) << i for i, r in enumerate(rows))
    if (target | pins) != full:
        return False
    optional = full ^ pins
    subset = optional
    while subset:
        subset = (subset - 1) & optional
        word = pins | subset
        if all((rows[i] & word).bit_count() % 2 == (target >> i & 1)
               for i in range(len(rows)) if word >> i & 1):
            return False
    return True


if __name__ == '__main__':
    count = Counter()
    examples = {}
    for graph in nx.graph_atlas_g():
        n = len(graph)
        if n < 4 or max(dict(graph.degree()).values()) > 5 or nx.node_connectivity(graph) < 3:
            continue
        rows = [sum(1 << j for j in graph[i]) for i in range(n)]
        for a, b in graph.edges:
            if witnesses(rows, a, b):
                pattern = tuple(sorted([len(graph[a]) % 2, len(graph[b]) % 2]))
                count[n, pattern] += 1
                examples.setdefault((n, pattern), (rows, (a, b)))
    print(sorted(count.items()))
    print(examples)
