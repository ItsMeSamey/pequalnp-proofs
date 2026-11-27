"""Compile a CNF to a signed cubic formula; check its emitted clauses over F3."""
from heapq import heapify, heappop, heappush
from itertools import product
from collections import defaultdict


class Graph:
    def __init__(self):
        self.activity = []
        self.edges = []

    def vertex(self, activity=1):
        self.activity.append(activity)
        return len(self.activity) - 1

    def edge(self, a, b):
        assert a != b
        self.edges.append(tuple(sorted((a, b))))


def weighted_source(n, clauses):
    graph = Graph()
    literals = {}
    for index in range(1, n + 1):
        a, b = graph.vertex(), graph.vertex()
        literals[index], literals[-index] = a, b
        penalty = graph.vertex(-1)
        for x, y in ((a, b), (a, penalty), (b, penalty)):
            graph.edge(x, y)
    for clause in clauses:
        penalty = graph.vertex(-1)
        for lit in sorted(set(clause)):
            graph.edge(penalty, literals[lit])
    return graph


def expand(source):
    graph = Graph()
    ports = defaultdict(list)
    for a, b in source.edges:
        p, q = graph.vertex(), graph.vertex()
        ports[a].append(p)
        ports[b].append(q)
        graph.edge(p, q)
    for v, activity in enumerate(source.activity):
        start, end = graph.vertex(activity), graph.vertex()
        chain = [start, *ports[v], end]
        for a, b in zip(chain, chain[1:]):
            for weight in (-1, -1, 1, -1, -1):
                mid = graph.vertex(weight)
                graph.edge(a, mid)
                a = mid
            graph.edge(a, b)
    negative = [i for i, weight in enumerate(graph.activity) if weight == -1]
    for v in negative:
        graph.activity[v] = 1
        graph.edge(v, graph.vertex())
    if len(negative) % 2:
        graph.vertex()
    return graph


def fragment(graph, prism):
    a, b, c, d, e, f = (graph.vertex() for _ in range(6))
    root = graph.vertex()
    if prism:
        edges = [(a,b),(b,c),(c,a),(d,e),(e,f),(f,d),(b,e),(c,f)]
    else:
        edges = [(x,y) for x in (a,b,c) for y in (d,e,f) if (x,y) != (a,d)]
    for u, v in [*edges, (root,a), (root,d)]:
        graph.edge(u,v)
    return root


def combine(graph, a, b):
    root = graph.vertex()
    graph.edge(root, a)
    graph.edge(root, b)
    return root


def compile_formula(n, clauses, normalize_count=False):
    graph = expand(weighted_source(n, clauses))
    degree = [0] * len(graph.activity)
    for a, b in graph.edges:
        degree[a] += 1
        degree[b] += 1
    for v, d in enumerate(degree):
        assert d <= 3
        for _ in range(3 - d):
            c = combine(graph, fragment(graph, False), fragment(graph, True))
            root = combine(graph, fragment(graph, False), c)
            graph.edge(v, root)
    if normalize_count and len(graph.edges) % 2:
        vertices = [graph.vertex() for _ in range(4)]
        for i, v in enumerate(vertices):
            for u in vertices[:i]:
                graph.edge(u,v)
    formula = [[] for _ in graph.activity]
    for i, (a,b) in enumerate(graph.edges, 1):
        formula[a].append(i)
        formula[b].append(-i)
    return formula


def contract_formula(formula, width_cap=12):
    """Recover edge tensors from signed literals, then eliminate clause spins."""
    occurs = defaultdict(list)
    for v, clause in enumerate(formula):
        assert len(clause) == len({abs(x) for x in clause}) == 3
        for lit in clause:
            occurs[abs(lit)].append((v, lit > 0))
    adj = {v: set() for v in range(len(formula))}
    buckets = {v: set() for v in adj}
    factors = {}
    next_id = 0

    def add(scope, values):
        nonlocal next_id
        for v in scope:
            buckets[v].add(next_id)
        factors[next_id] = scope, values
        next_id += 1

    for v in adj:
        add((v,), [1, 2])
    for pair in occurs.values():
        assert len(pair) == 2
        (u, sign_u), (v, sign_v) = pair
        assert sign_u != sign_v and u != v and v not in adj[u]
        adj[u].add(v)
        adj[v].add(u)
        # Sum both raw bit values at their interpolation weights, retaining
        # only assignments falsifying every selected endpoint literal.
        table = []
        for mask in range(4):
            table.append(sum(2 for bit in (0,1)
                             if not (mask & 1 and bit == sign_u)
                             and not (mask & 2 and bit == sign_v)) % 3)
        add((u,v), table)
    heap = [(len(nbs),v) for v,nbs in adj.items()]
    heapify(heap)
    scalar = 1
    while adj:
        d,v = heappop(heap)
        if v not in adj or len(adj[v]) != d:
            continue
        assert d <= width_cap, (v,d)
        boundary = tuple(sorted(adj[v]))
        local = (v, *boundary)
        work = []
        for fid in tuple(buckets[v]):
            scope, table = factors.pop(fid)
            for x in scope:
                buckets[x].remove(fid)
            work.append(([local.index(x) for x in scope], table))
        out = [0] * (1 << d)
        for mask in range(1 << (d + 1)):
            value = 1
            for positions, table in work:
                index = sum(((mask >> pos) & 1) << j for j,pos in enumerate(positions))
                value = value * table[index] % 3
            out[mask >> 1] = (out[mask >> 1] + value) % 3
        if boundary:
            add(boundary, out)
        else:
            scalar = scalar * out[0] % 3
        del adj[v]
        for x in boundary:
            adj[x].remove(v)
            adj[x].update(y for y in boundary if y != x)
            heappush(heap,(len(adj[x]),x))
    return scalar, len(occurs)


def main():
    cases = [(0, []), (0,[()]), (1,[(1,)]), (1,[(1,),(-1,)]),
             (2,[(1,2)]), (2,[(1,1,-1)]), (2,[(1,2),(-1,2)])]
    for n, clauses in cases:
        expected = sum(all(any(bits[abs(x)-1] == (x > 0) for x in clause)
                           for clause in clauses) for bits in product((0,1), repeat=n)) % 3
        for normalize in (False, True):
            value, m = contract_formula(compile_formula(n, clauses, normalize))
            observed = value * pow(2, m, 3) % 3 if normalize else value
            assert observed == expected, (n, clauses, normalize, observed, expected)
    print(f"{len(cases)} source cases, both normalizations passed")


if __name__ == "__main__":
    main()
