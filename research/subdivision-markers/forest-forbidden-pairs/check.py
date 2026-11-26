"""Enumerate all binary boundary solutions of the emitted graph, then check forbidden pairs."""
from collections import Counter, defaultdict
from itertools import product
from math import prod
from random import Random
import networkx as nx


def make_graph(rows):
    graph = nx.Graph()
    edges = []
    ports = []
    designated = {}
    truth_edges = {}
    conflicts = []
    clusters = []

    def new_vertices(count):
        start = len(graph)
        result = list(range(start, start + count))
        graph.add_nodes_from(result)
        return result

    def edge(a, b):
        assert a != b and not graph.has_edge(a, b)
        graph.add_edge(a, b)
        edges.append((a, b))
        return len(edges) - 1

    by_var = defaultdict(list)
    for j, row in enumerate(rows):
        for k, (v, neg) in enumerate(row):
            by_var[v].append((j, k, neg))
    for v, occurrences in sorted(by_var.items()):
        cycle = new_vertices(2 * max(2, len(occurrences)))
        ids = [edge(cycle[i-1], cycle[i]) for i in range(len(cycle))]
        truth_edges[v] = ids[0]  # Even edges are selected in the true state.
        for i, (j, k, neg) in enumerate(occurrences):
            designated[j, k] = ids[2*i + (1-neg)]
        ports.append(cycle[0])
        clusters.append(cycle)

    for j, row in enumerate(rows):
        block = new_vertices(8)
        left, right = block[:2]
        for k in range(3):
            a, b = block[2+2*k:4+2*k]
            first = edge(left, a)
            edge(a, b)
            edge(b, right)
            conflicts.append((first, designated[j, k]))
        ports.append(block[2])
        clusters.append(block)
    spine = new_vertices(2*len(ports))
    for a, b in zip(spine, spine[1:]):
        edge(a, b)
    for j, (port, cluster) in enumerate(zip(ports, clusters)):
        edge(port, spine[2*j])
        cluster.extend(spine[2*j:2*j+2])
    order = [v for cluster in clusters for v in cluster]
    return graph, edges, conflicts, truth_edges, order


def odd_solutions(graph, edges):
    indices = {tuple(sorted(pair)): i for i, pair in enumerate(edges)}
    tree = list(nx.bfs_edges(graph, 0))
    tree_ids = [indices[tuple(sorted(pair))] for pair in tree]

    def complete(chords, demand):
        mask = 0
        for i in chords:
            mask |= 1 << i
            u, v = edges[i]
            demand ^= (1 << u) | (1 << v)
        for (p, v), i in reversed(list(zip(tree, tree_ids))):
            if demand & (1 << v):
                mask |= 1 << i
                demand ^= (1 << v) | (1 << p)
        assert demand == 0
        return mask

    particular = complete([], (1 << len(graph)) - 1)
    chords = sorted(set(range(len(edges))) - set(tree_ids))
    homogeneous = [complete([i], 0) for i in chords]
    yield particular
    # Successive Gray-code solutions differ by one fundamental cycle.
    for i in range(1, 1 << len(chords)):
        particular ^= homogeneous[(i & -i).bit_length()-1]
        yield particular


def check_rows(rows):
    graph, edges, pairs, truth, order = make_graph(rows)
    assert nx.is_connected(graph) and nx.is_bipartite(graph)
    assert nx.check_planarity(graph)[0] and max(dict(graph.degree()).values()) <= 3
    assert nx.approximation.treewidth_min_degree(graph)[0] <= 2
    assert len(graph) % 2 == 0 and len(graph) == len(order)
    assert len(set(i for pair in pairs for i in pair)) == 2*len(pairs) == 6*len(rows)
    positions = {v: i for i, v in enumerate(order)}
    max_occ = max(sum(a == v for row in rows for a, _ in row) for v in truth)
    if max_occ <= 4:
        assert max(abs(positions[u]-positions[v]) for u,v in edges) <= 19
    degrees = [0] * len(graph)
    for i, (u, v) in enumerate(edges):
        degrees[u] |= 1 << i
        degrees[v] |= 1 << i
    found, matchings = Counter(), Counter()
    pair_masks = [(1 << a) | (1 << b) for a,b in pairs]
    variables = sorted(truth)
    unguarded = 0
    for mask in odd_solutions(graph, edges):
        unguarded += 1
        counts = [(mask & d).bit_count() for d in degrees]
        assert all(k in (1,3) for k in counts)
        centers = [u for u, k in enumerate(counts) if k == 3]
        center_set = set(centers)
        for u in centers:
            for v in graph[u]:
                if v in center_set:
                    assert not (mask & degrees[u] & degrees[v])
        if any(mask & pm == pm for pm in pair_masks):
            continue
        x = tuple((mask >> truth[v]) & 1 for v in variables)
        found[x] += 1
        matchings[x] += not centers
    assert unguarded == 2 ** (len(variables) + 2*len(rows))
    for x in product(range(2), repeat=len(variables)):
        assignment = dict(zip(variables, x))
        true_counts = [sum(assignment[v] ^ neg for v,neg in row) for row in rows]
        assert found[x] == prod(2**(n-1) if n else 0 for n in true_counts)
        assert matchings[x] == prod(true_counts)
    return unguarded, sum(found.values())


if __name__ == '__main__':
    cases = []
    for signs in product(range(2), repeat=6):
        cases.append([tuple((i, signs[j*3+i]) for i in range(3)) for j in range(2)])
    unit = lambda v, neg: ((v, neg),)*3
    cases += [[unit(0,0)], [unit(0,0),unit(0,1)],
              [[(0,0),(0,1),(1,1)],unit(1,0)], [[(0,0),(1,0),(2,1)]]]
    rng = Random(408)
    for _ in range(42):
        n = rng.randint(1,3)
        cases.append([[(rng.randrange(n),rng.randrange(2)) for _ in range(3)]
                      for _ in range(rng.randint(1,4))])
    checks = [check_rows(rows) for rows in cases]
    assert any(n == 0 for _,n in checks) and any(n > 0 for _,n in checks)
    print(len(cases), 'graphs;', sum(n for n,_ in checks), 'all-odd subgraphs;',
          sum(n == 0 for _,n in checks), 'UNSAT instances')
