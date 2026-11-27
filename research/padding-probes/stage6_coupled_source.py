"""Independent-set controls for the original strict source and fixed paired-triple DFA."""
from itertools import combinations

from padding_cnf import encode, parse
from stage6_source_solver import compile_source


def source_from_edges(n, edges):
    """Return (source variable count, strict clauses), padding each edge with ±z first."""
    edges = tuple(edges)
    if type(n) is not int or n < 1:
        raise ValueError("positive graph order required")
    normalized = set()
    for e in edges:
        if len(e) != 2 or any(type(v) is not int or not 0 <= v < n for v in e) or e[0] == e[1]:
            raise ValueError("expected a loopless graph with zero-based integer vertices")
        edge = tuple(sorted(e))
        if edge in normalized:
            raise ValueError("duplicate edge")
        normalized.add(edge)
    if {v for e in normalized for v in e} != set(range(n)):
        raise ValueError("isolated vertices are outside this control")
    z = n + 1
    clauses = tuple((pad, -(u + 1), -(v + 1)) for u, v in sorted(normalized) for pad in (z, -z))
    return z, clauses


def triangle_benchmark(base_order=4, base_edges=None):
    """Default is K4; passing any simple cubic expander gives its triangle replacement."""
    if base_edges is None:
        if base_order != 4:
            raise ValueError("supply base_edges outside the K4 default")
        base_edges = tuple(combinations(range(4), 2))
    base_edges = tuple(base_edges)
    source_from_edges(base_order, base_edges)  # Validate the simple graph before lifting it.
    neighborhoods = [[] for _ in range(base_order)]
    for u, v in base_edges:
        neighborhoods[u].append(v)
        neighborhoods[v].append(u)
    if any(len(ns) != 3 for ns in neighborhoods):
        raise ValueError("triangle replacement expects a cubic base")
    ports = {(u, v): 3 * u + j for u, ns in enumerate(neighborhoods)
             for j, v in enumerate(sorted(ns))}
    triangles = [tuple(range(3 * u, 3 * u + 3)) for u in range(base_order)]
    edges = [e for group in triangles for e in combinations(group, 2)]
    edges.extend((ports[u, v], ports[v, u]) for u, v in base_edges)
    n = 3 * base_order
    source_n, clauses = source_from_edges(n, edges)
    job = compile_source(source_n, clauses, exact_twice=True)
    yes = job.word(0)
    slots, immutable, key = parse(yes)
    no = encode(immutable, slots, key & ~(1 << slots))
    return dict(source_n=source_n, clauses=clauses, graph_order=n, graph_edges=tuple(edges),
                triangles=tuple(triangles), job=job, raw_witnesses={0:no, 1:yes})
