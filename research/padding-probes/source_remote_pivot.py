"""Sparse width-three CNF decision by conditional binary representations."""
from collections.abc import Mapping
from itertools import product
from source_easy_prepass import _binary


def solve(n, clauses, *, source_pins=(), discovery_cap=None, branch_cap=None):
    """Discovery charges each clause inspection and each singleton feasibility call.
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
    stats = dict(discovery_work=0, projection_calls=0, branch_calls=0, base_binary_rows=0)
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
    names = sorted({abs(x) for row in residual for x in row})

    class Cutoff(Exception):
        pass

    def charge():
        if discovery_cap is not None and stats['discovery_work'] >= discovery_cap:
            raise Cutoff
        stats['discovery_work'] += 1

    def separator(row, condition):
        # A missing singleton permits deleting its only true literal. If all
        # three extend, their majority falsifies the row but preserves 2-CNF.
        for i, literal in enumerate(row):
            units = tuple((x if j==i else -x,) for j,x in enumerate(row))
            charge()
            stats['projection_calls'] += 1
            if _binary(binary + condition + units) is None:
                return tuple(x for x in row if x != literal)
        return None

    covers = {}
    pending = set()
    common = []
    try:
        for i,row in enumerate(triples):
            charge()
            reduced = separator(row, ())
            if reduced is None:
                pending.add(i)
            else:
                common.append(reduced)
        stats['base_binary_rows'] = len(common)
        if pending:
            for w in names:
                pieces = {}
                for i in sorted(pending):
                    charge()
                    zero = separator(triples[i], ((-w,),))
                    if zero is not None:
                        one = separator(triples[i], ((w,),))
                        if one is not None:
                            pieces[i] = (zero, one)
                if pieces:
                    covers[w] = pieces
    except Cutoff:
        return result("UNKNOWN", "discovery cap")

    owned = {}
    while pending:
        w = max(covers, key=lambda v: len(pending.intersection(covers[v])))
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
