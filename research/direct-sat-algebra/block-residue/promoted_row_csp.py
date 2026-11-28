"""Prune and promote NAND cone tables before exact row interaction solving."""

from itertools import combinations, product

from corridor_nand import _hull, _net, _replay, _rows, _sat
from row_csp import _prepare, _relations, _tree


def _promote(n, base, tables, stats):
    while True:
        if _sat(n, base) is None:
            return None
        pending = []
        changed = False
        for table in tables:
            kept = [row for row in table if _sat(n, base + row) is not None]
            stats["pruned"] += len(table) - len(kept)
            if not kept:
                return None
            ports = [abs(l)-1 for l, in kept[0]]
            words = [tuple(int(l>0) for l, in row) for row in kept]
            closed = all(tuple((x&y)|(x&z)|(y&z) for x,y,z in zip(a,b,c)) in words
                         for a,b,c in combinations(words, 3))
            if closed:
                base.extend(_hull(ports, words))
                stats["promoted"] += 1
                stats["bad"] -= 1
                changed = True
            else:
                pending.append(kept)
        if not changed:
            return pending
        tables = pending


def _choose(n, base, rows, stats, cap):
    pairwise = _relations(n, base, rows)
    if pairwise is None:
        return "unsat", None
    domains, relations = pairwise
    chosen = {}
    for root in range(len(rows)):
        if root in chosen:
            continue
        order = [root]
        parent = {root: None}
        for i in order:
            for j in relations[i]:
                if j not in parent:
                    parent[j] = i
                    order.append(j)
        edges = [(i,j) for i in order for j in relations[i] if i < j]
        if len(edges) == len(order)-1:
            stats["forest_components"] += 1
            assignment = _tree(order, parent, domains, relations)
            if assignment is None:
                return "unsat", None
        else:
            stats["cyclic_components"] += 1
            for values in product(*(domains[i] for i in order)):
                if cap is not None and stats["searched"] >= cap:
                    return "skip", None
                stats["searched"] += 1
                assignment = dict(zip(order, values))
                if all((assignment[i], assignment[j]) in relations[i][j] for i,j in edges):
                    break
            else:
                return "unsat", None
        chosen.update(assignment)
    return "sat", chosen


def solve(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None,
          max_bad=None, max_search=None):
    """Return status, statistics and raw input bits.

    Conditioning discards an actual row only when its entire set of unit pins
    contradicts the shared binary base. A majority-closed surviving table
    equals its binary hull and can enter that base. Each extra pass retires
    at least one table, so promotion costs polynomial time and space.
    max_bad applies after promotion. max_search counts cyclic tuples tested.
    """
    gates = _net(inputs, gates)
    for cap in (max_bad, max_search):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("invalid cap")
    if output is not None:
        if type(output) is not int or not 0 <= output < inputs+len(gates):
            raise ValueError("invalid output")
        pins = tuple(pins) + ((output, 1),)
    original = _rows(inputs+len(gates), clauses, pins, equalities)
    physical, expanded, aliases, base, factors, tables = _prepare(inputs, gates, original)
    n = inputs + len(physical)
    stats = dict(initial_bad=len(tables), bad=len(tables), promoted=0, pruned=0,
                 forest_components=0, cyclic_components=0, searched=0)
    rows = _promote(n, base, tables, stats)
    if rows is None:
        return "unsat", stats, None
    if max_bad is not None and len(rows) > max_bad:
        return "skip", stats, None
    status, chosen = _choose(n, base, rows, stats, max_search)
    if status != "sat":
        return status, stats, None
    full = base.copy()
    for i, side in chosen.items():
        full.extend(rows[i][side])
    model = _sat(n, full)
    if model is None:
        raise AssertionError("compatible remaining rows did not integrate")
    raw = model[:inputs]
    for ports, entries, traces in factors:
        choice = traces[tuple(model[w] for w in ports)]
        for w, bit in zip(entries, choice):
            if w < inputs:
                raw[w] = bit
    material = _replay(raw, physical)
    wires = _replay(raw, gates)
    if any(w != ((0 if v == -1 else material[expanded[v]]) ^ flip)
           for w, (v, flip) in zip(wires, aliases)):
        raise AssertionError("original alias replay failed")
    if any(not any(material[abs(l)-1] == (l > 0) for l in row) for row in full):
        raise AssertionError("promoted or selected rows failed replay")
    if any(not any(wires[abs(l)-1] == (l > 0) for l in row) for row in original):
        raise AssertionError("original exterior or output failed replay")
    return "sat", stats, tuple(raw)
