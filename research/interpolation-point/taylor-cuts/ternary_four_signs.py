"""Full-support ternary systems of row width at most four."""
from collections import defaultdict
from itertools import combinations, product

import networkx as nx


def occurrences(rows):
    ports = defaultdict(list)
    for i, row in enumerate(rows):
        for x, c in row.items():
            ports[x].append((i, c))
    return ports


def euler(rows):
    graph = nx.MultiGraph()
    for x, ports in occurrences(rows).items():
        graph.add_edge(ports[0][0], ports[1][0] if len(ports) == 2 else -1, key=x)
    signs = {}
    for vertices in nx.connected_components(graph):
        start = -1 if -1 in vertices else min(vertices)
        arrival = first = None
        for u, v, x in nx.eulerian_circuit(graph.subgraph(vertices), source=start, keys=True):
            signs[x] = 1 if u == -1 or arrival is None else -arrival * rows[u][x] % 3
            if first is None and start != -1:
                first = signs[x] * rows[u][x]
            arrival = None if v == -1 else signs[x] * rows[v][x]
        if start != -1 and (first + arrival) % 3:
            return None
    return signs


def matching(rows, quotas):
    graph = nx.Graph()
    for i, (row, quota) in enumerate(zip(rows, quotas)):
        for x in row:
            graph.add_node(('p', i, x))
        for j in range(quota):
            graph.add_node(('s', i, j))
            for x in row:
                graph.add_edge(('s', i, j), ('p', i, x))
    ports = occurrences(rows)
    singles = []
    for x, pair in ports.items():
        i, c = pair[0]
        port = ('p', i, x)
        if len(pair) == 1:
            singles.append(port)
        else:
            j, d = pair[1]
            other = ('p', j, x)
            if c == d:
                graph.add_edge(port, other)
            else:
                graph.add_edge(port, ('o', x))
                graph.add_edge(other, ('o', x))
    if len(graph) % 2:
        singles.append(('pad',))
        graph.add_node(('pad',))
    graph.add_edges_from(combinations(singles, 2))
    pairs = nx.max_weight_matching(graph, maxcardinality=True)
    if 2 * len(pairs) != len(graph):
        return None
    mate = dict(pairs)
    mate.update((v, u) for u, v in pairs)
    signs = {}
    for x, pair in ports.items():
        i, c = pair[0]
        signs[x] = c if mate['p', i, x][0] == 's' else 3 - c
    return signs


def solve(rows, rhs=None, *, n=None, high_cap=0, ambiguous_cap=0):
    rows = [tuple(c % 3 for c in row) for row in rows]
    n = len(rows[0]) if n is None and rows else (n or 0)
    rhs = [0]*len(rows) if rhs is None else [b % 3 for b in rhs]
    if n < 0 or len(rhs) != len(rows) or any(len(row) != n for row in rows):
        raise ValueError('bad dimensions')
    stats = dict(links=0, high=0, matching_calls=0)
    parent, weight = list(range(n)), [1]*n

    def find(x):
        c = 1
        while x != parent[x]:
            c = c * weight[x] % 3
            x = parent[x]
        return x, c

    def result(signs):
        if signs is None:
            return 'UNSAT', None, stats
        witness = tuple(find(x)[1]*signs.get(find(x)[0], 1) % 3 for x in range(n))
        assert all(sum(a*b for a,b in zip(row,witness)) % 3 == t for row,t in zip(rows,rhs))
        return 'SAT', witness, stats

    while True:
        reduced, targets = [], []
        changed = False
        for dense, target in zip(rows, rhs):
            merged = defaultdict(int)
            for x,c in enumerate(dense):
                if c:
                    root, w = find(x)
                    merged[root] += c*w
            row = {x:c%3 for x,c in merged.items() if c%3}
            if not row:
                if target:
                    return result(None)
                continue
            if len(row) == 1 and target == 0:
                return result(None)
            if target == 0 and len(row) in (2,3):
                (x,c), *rest = row.items()
                for y,d in rest:
                    parent[y] = x
                    weight[y] = (1 if len(row) == 3 else -1)*c*d % 3
                    stats['links'] += 1
                changed = True
                break
            reduced.append(row)
            targets.append(target)
        if not changed:
            break
    if any(len(row)>4 for row in reduced):
        return 'UNKNOWN', None, stats
    high = sorted(x for x,lst in occurrences(reduced).items() if len(lst)>2)
    stats['high'] = len(high)
    if not high and not any(targets):
        stats['backend'] = 'euler'
        return result(euler(reduced))
    if len(high)>high_cap:
        return 'UNKNOWN', None, stats
    stats['backend'] = 'matching'
    skipped = False
    for assignment in product((1,2),repeat=len(high)):
        pins = dict(zip(high,assignment))
        low, choices = [], []
        for row,b in zip(reduced,targets):
            residual = {x:c for x,c in row.items() if x not in pins}
            positives = sum(c*pins[x]%3 == 1 for x,c in row.items() if x in pins)
            choices.append([q for q in range(len(residual)+1)
                            if (2*(q+positives)-len(row))%3 == b])
            low.append(residual)
        if not all(choices):
            continue
        if sum(len(c)>1 for c in choices)>ambiguous_cap:
            skipped = True
            continue
        for quotas in product(*choices):
            stats['matching_calls'] += 1
            signs = matching(low,quotas)
            if signs is not None:
                return result(pins | signs)
    return ('UNKNOWN',None,stats) if skipped else result(None)
