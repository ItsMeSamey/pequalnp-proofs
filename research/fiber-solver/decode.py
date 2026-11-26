"""Recover block bits from full-scope truth-table CNF (no auxiliaries)."""
from collections import defaultdict
from itertools import product
from fibers import solve


def decode(clauses, variables):
    """Assumes signed, nonzero DIMACS literals and positive variable indices.

    Returns tri-state as in fibers.solve. Explicit expansion can be exponential
    in the largest clause width, even for sparse forbidden tables.
    """
    variables = set(variables)
    if any(not isinstance(x, int) or x <= 0 for x in variables):
        raise ValueError("variable indices must be positive integers")
    forbidden = defaultdict(set)
    for clause in clauses:
        lits = set(clause)
        scope = frozenset(map(abs, lits))
        if 0 in scope or not scope <= variables:
            raise ValueError("unknown variable")
        if any(-lit in lits for lit in lits):
            continue
        if not scope:
            return 'unsat', None
        forbidden[scope].add(frozenset(-lit for lit in lits if lit < 0))
    groups = defaultdict(list)
    for x in sorted(variables):
        groups[frozenset(s for s in forbidden if x in s)].append(x)
    blocks = [tuple(bits) for sig, bits in groups.items() if sig]
    domains = {b: list(product((0, 1), repeat=len(b))) for b in blocks}
    edges = []
    for scope, bad in forbidden.items():
        endpoints = [b for b in blocks if b[0] in scope]
        if len(endpoints) > 2:
            return 'unsupported', None
        def ones(b, val):
            return frozenset(x for x, flag in zip(b, val) if flag)
        a = endpoints[0]
        if len(endpoints) == 1:
            domains[a] = [val for val in domains[a] if ones(a, val) not in bad]
        else:
            b = endpoints[1]
            edges.append((a, b, [(x,y) for x in domains[a] for y in domains[b]
                                 if (ones(a,x) | ones(b,y)) not in bad]))
    status, values = solve(domains, edges)
    if status != 'sat':
        return status, None
    witness = dict.fromkeys(variables, 0)
    for b, val in values.items():
        witness.update(zip(b, val))
    return status, witness
