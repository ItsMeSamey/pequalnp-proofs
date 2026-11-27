"""Exact atlas census through order eight by removing the unique leaf."""
from collections import Counter
from itertools import combinations
import networkx as nx


def odd(rows, mask):
    return all((row & mask).bit_count() % 2 for i, row in enumerate(rows) if mask >> i & 1)


def main():
    hosts = Counter()
    successes = []
    for graph in nx.graph_atlas_g():
        n = len(graph)
        if n not in (1, 3, 5, 7) or not nx.is_connected(graph):
            continue
        even = [i for i in graph if graph.degree(i) % 2 == 0]
        if len(even) != 1 or graph.degree(even[0]) not in (2, 4):
            continue
        parent = even[0]
        if any(graph.degree(i) not in (3, 5) for i in graph if i != parent):
            continue
        rows = [sum(1 << j for j in graph[i]) for i in graph] + [1 << parent]
        rows[parent] |= 1 << n
        full = (1 << (n + 1)) - 1
        assert odd(rows, full)
        hosts[n + 1] += 1
        pairs = []
        for p, q in combinations(range(n), 2):
            pins = (1 << p) | (1 << q)
            words = [w for w in range(full + 1) if w & pins == pins and odd(rows, w)]
            if words == [full]:
                pairs.append((p, q))
        if pairs:
            successes.append((rows, pairs))
    print('eligible hosts', sorted(hosts.items()))
    for rows, pairs in successes:
        print('rows', rows, 'pin pairs', pairs)
    assert hosts == {6: 2, 8: 47}
    assert len(successes) == 4 and sum(len(pairs) for _, pairs in successes) == 7


if __name__ == '__main__':
    main()
