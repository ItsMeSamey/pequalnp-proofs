"""Compile Hs=0 with all coordinates nonzero over GF(3) to graph 3-colouring."""
from dataclasses import dataclass
from itertools import combinations


@dataclass
class Graph:
    order: int
    edges: set
    anchors: list
    occurrences: list
    rows: list

    def vertices(self, count):
        start = self.order
        self.order += count
        return tuple(range(start, self.order))

    def triangle(self, sites):
        self.edges.update(tuple(sorted(edge)) for edge in combinations(sites, 2))

    def matching(self, left, right):
        self.edges.update(tuple(sorted(edge)) for edge in zip(left, right))


def compile_graph(n, rows):
    if n < 0:
        raise ValueError("negative number of columns")
    normalized = []
    for row in rows:
        if len(row) != n:
            raise ValueError("wrong row length")
        normalized.append(tuple((i, c % 3) for i, c in enumerate(row) if c % 3))
    graph = Graph(0, set(), [], [], normalized)
    if any(len(row) == 1 for row in normalized):
        graph.edges.update(combinations(graph.vertices(4), 2))
        return graph
    for _ in range(n):
        anchor = graph.vertices(3)
        graph.triangle(anchor)
        graph.anchors.append(anchor)
    for row in normalized:
        joints = graph.vertices(len(row))
        for k, (i, c) in enumerate(row):
            u, v = joints[k], joints[(k + 1) % len(row)]
            first, second = (u, v) if c == 1 else (v, u)
            occurrence = (first, second, graph.vertices(1)[0])
            middle = graph.vertices(3)
            graph.triangle(occurrence)
            graph.triangle(middle)
            graph.matching(graph.anchors[i], middle)
            graph.matching(middle, occurrence)
            graph.occurrences.append((i, middle, occurrence))
    return graph


def decode(graph, colours):
    if len(colours) != graph.order or any(c not in (0, 1, 2) for c in colours):
        raise ValueError("invalid palette or length")
    if any(colours[u] == colours[v] for u, v in graph.edges):
        raise ValueError("improper colouring")
    return tuple((colours[a[1]] - colours[a[0]]) % 3 for a in graph.anchors)


def encode(graph, signs):
    if any(len(row) == 1 for row in graph.rows):
        raise ValueError("singleton contradiction")
    if len(signs) != len(graph.anchors) or any(s not in (1, 2) for s in signs):
        raise ValueError("invalid nonzero field vector")
    if any(sum(signs[i] * c for i, c in row) % 3 for row in graph.rows):
        raise ValueError("nonzero syndrome")
    colours = [None] * graph.order

    def assign(sites, shift, slope):
        for j, vertex in enumerate(sites):
            colour = (shift + j * slope) % 3
            assert colours[vertex] in (None, colour)
            colours[vertex] = colour

    for a, s in zip(graph.anchors, signs):
        assign(a, 0, s)
    copies = iter(graph.occurrences)
    for row in graph.rows:
        value = 0
        for i, c in row:
            _, middle, occurrence = next(copies)
            after = (value + signs[i] * c) % 3
            offset = value if c == 1 else after
            assign(occurrence, offset, signs[i])
            assign(middle, next(t for t in (1, 2) if t != offset), signs[i])
            value = after
    return tuple(colours)
