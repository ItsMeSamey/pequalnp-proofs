"""Sparse semantic pivots discovered by implication walks from clause singletons."""
from collections.abc import Mapping
from itertools import product
from source_easy_prepass import _binary


def solve(n, clauses, *, source_pins=(), discovery_cap=None, branch_cap=None):
    """Discovery charges feasibility calls, visited vertices/edges and stored candidate records.
    Branches charge one full pivot assignment. Parsing and greedy cover are polynomial.
    """
    if type(n) is not int or n < 0:
        raise ValueError("invalid arity")
    for cap in (discovery_cap, branch_cap):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("invalid cap")
    original = tuple(tuple(row) for row in clauses)
    if any(len(row)>3 or any(type(x) is not int or not 1<=abs(x)<=n for x in row)
           for row in original):
        raise ValueError("invalid source clause")
    items = source_pins.items() if isinstance(source_pins, Mapping) else source_pins
    pins = tuple(tuple(pair) for pair in items)
    fixed = {}
    conflict = False
    for v, bit in pins:
        if type(v) is not int or not 1<=v<=n or type(bit) is not int or bit not in (0,1):
            raise ValueError("invalid source pin")
        conflict |= v in fixed and fixed[v] != bit
        fixed[v] = bit
    stats = dict(discovery_work=0, projection_calls=0, branch_calls=0, base_binary_rows=0,
                 implication_vertices=0, implication_edges=0, candidate_records=0)
    selected = []

    def result(status, reason=None, true=None):
        return dict(status=status, true_variables=true, pivots=tuple(selected),
                    metrics=stats, reason=reason)

    if conflict:
        return result("UNSAT")
    residual = set()
    for row in original:
        lits = set(row)
        if any(-x in lits or fixed.get(abs(x)) == int(x>0) for x in lits):
            continue
        live = tuple(sorted(x for x in lits if abs(x) not in fixed))
        if not live:
            return result("UNSAT")
        residual.add(live)
    binary = tuple(sorted(r for r in residual if len(r)<=2))
    triples = tuple(sorted(r for r in residual if len(r)==3))

    class Cutoff(Exception):
        pass

    def charge():
        if discovery_cap is not None and stats['discovery_work'] >= discovery_cap:
            raise Cutoff
        stats['discovery_work'] += 1

    def feasible(units):
        charge()
        stats['projection_calls'] += 1
        return _binary(binary + tuple((x,) for x in units)) is not None

    graph = {}
    for row in binary:
        a,b = row[0],row[-1]
        graph.setdefault(-a, []).append(b)
        graph.setdefault(-b, []).append(a)

    def consequences(units):
        # Fixed backbone facts need not be added: they cannot have a
        # feasible opposite singleton. All varying forced literals are
        # reachable from one of the three pins in the implication graph.
        seen = set(units)
        stack = list(units)
        while stack:
            charge()
            stats['implication_vertices'] += 1
            x = stack.pop()
            for y in graph.get(x, ()):
                charge()
                stats['implication_edges'] += 1
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return seen

    covers = {}
    pending = set()
    common = []
    try:
        if not feasible(()):
            return result("UNSAT")
        for i,row in enumerate(triples):
            singletons = []
            for j in range(3):
                units = tuple(x if k == j else -x for k,x in enumerate(row))
                if not feasible(units):
                    common.append(row[:j]+row[j+1:])
                    break
                singletons.append(units)
            else:
                pending.add(i)
                forces = {}
                for j,units in enumerate(singletons):
                    for lit in consequences(units):
                        forces.setdefault(lit, j)
                for w,j in forces.items():
                    if w > 0 and -w in forces:
                        charge()
                        stats['candidate_records'] += 1
                        k = forces[-w]
                        # When w=0, the singleton forcing +w is missing.
                        # When w=1, use the singleton forcing -w instead.
                        halves = row[:j]+row[j+1:], row[:k]+row[k+1:]
                        covers.setdefault(w, {})[i] = halves
        stats['base_binary_rows'] = len(common)
    except Cutoff:
        return result("UNKNOWN", "discovery cap")

    owned = {}
    while pending:
        w = min(covers, key=lambda v: (-len(pending.intersection(covers[v])), v))
        hits = sorted(pending.intersection(covers[w]))
        if not hits:
            raise ArithmeticError("clause-local pivot missing")
        selected.append(w)
        owned[w] = [covers[w][i] for i in hits]
        pending.difference_update(hits)

    for bits in product((0, 1), repeat=len(selected)):
        if branch_cap is not None and stats['branch_calls'] >= branch_cap:
            return result("UNKNOWN", "branch cap")
        stats['branch_calls'] += 1
        rows = list(binary) + common
        for w, bit in zip(selected, bits):
            rows.append((w if bit else -w,))
            rows.extend(halves[bit] for halves in owned[w])
        model = _binary(rows)
        if model is None:
            continue
        true = tuple(sorted(v for v, bit in (fixed | model).items() if bit))
        ids = set(true)
        if (any(not any((abs(x) in ids)==(x>0) for x in row) for row in original)
                or any(int(v in ids)!=bit for v,bit in pins)):
            raise ArithmeticError("invalid original source witness")
        return result("SAT", true=true)
    return result("UNSAT")
