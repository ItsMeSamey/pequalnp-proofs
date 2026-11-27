"""Recognize exactly ordered selector-free outputs of compile_nonzero, sans metadata."""
from read_two_ring_nonzero import compile_nonzero


def _candidate(clauses, edges, sites, original_edges, original_sites, variables):
    # Each half-edge ID occurs once among the endpoint clauses. Its other
    # occurrence is at the edge's own middle clause, verified on recompilation.
    endpoints = [None] * (2 * edges)
    for c, row in enumerate(clauses[:sites]):
        for i in row:
            if i < len(endpoints):
                if endpoints[i] is not None:
                    return None
                endpoints[i] = c
    if None in endpoints:
        return None
    owners = {}
    site = link_edge = 0
    for v in range(original_sites):
        if link_edge >= edges - original_edges:
            return None
        a, b = endpoints[2*link_edge:2*link_edge+2]
        degree = b - site - 2
        if a != site or degree < 0 or site + 7 + 6*degree > sites:
            return None
        for copy in range(site+1, site+degree+1):
            owners[copy] = v
        site += 7 + 6*degree
        link_edge += 6 * (degree+1)
    if site != sites or link_edge != edges - original_edges:
        return None
    raw = [[] for _ in range(original_sites-3*variables)]
    for edge in range(link_edge+3*variables, edges):
        a, b = endpoints[2*edge:2*edge+2]
        owner, lit = owners.get(a, -1), owners.get(b, -1)
        if not 3*variables <= owner < original_sites or not 0 <= lit < 3*variables:
            return None
        if lit % 3 == 2:
            return None
        literal = lit // 3 + 1
        raw[owner-3*variables].append(literal if lit % 3 == 0 else -literal)
    return tuple(map(tuple, raw))


def recover(n, clauses, point, k):
    """Return (number of source variables, deduplicated source clauses) or None.

    Raw n and k must be Python ints and the point must use canonical residues,
    exactly as emitted. Ordered clause/point sequences may be lists or tuples.
    """
    if type(n) is not int or type(k) is not int or not 0 <= n or k < 1:
        return None
    if not isinstance(point, (tuple, list)) or len(point) != n:
        return None
    if not isinstance(clauses, (tuple, list)):
        return None
    if any(type(a) is not int or a < 0 for a in point):
        return None
    if any(not isinstance(row, (tuple, list)) or len(row) > 3 or
           any(type(a) is not int or not 0 <= a < n for a in row)
           for row in clauses):
        return None
    rows = tuple(map(tuple, clauses))
    values = tuple(point)
    # Raw variables = 46e + 26v + 1, clauses = 45e + 27v + 2.
    e_num = 27*(n-1) - 26*(len(rows)-2)
    v_num = 46*(len(rows)-2) - 45*(n-1)
    if min(e_num, v_num) < 0 or e_num % 72 or v_num % 72:
        return None
    original_edges, original_sites = e_num//72, v_num//72
    edges = 13*original_edges + 6*original_sites
    sites = 12*original_edges + 7*original_sites
    variables = k-edges-1
    if variables < 0 or 3*variables > min(original_sites, original_edges):
        return None
    source = _candidate(rows, edges, sites, original_edges, original_sites, variables)
    if source is None:
        return None
    test = compile_nonzero(variables, source)
    if (test["n"], test["clauses"], test["point"], test["k"]) == (n, rows, values, k):
        return variables, source
    return None
