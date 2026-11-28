"""Exact row-choice CSP for projected signed NAND cones."""
from itertools import combinations, product

from corridor_nand import _net, _replay, _rows, _sat
from distinct_cones import cone_groups
from joint_choice import _tables
from signed_cone_nand import _materialize, _translated, normalize


def _prepare(inputs, gates, original):
    retained, aliases = normalize(inputs, gates)
    groups = cone_groups(inputs, [(a[0], b[0]) for a, b in retained])
    if groups is None:
        raise AssertionError("tied operand after signed normalization")
    physical, expanded, blocks = _materialize(inputs, retained, groups)
    exterior = [tuple((expanded[abs(l)-1]+1)*(1 if l>0 else -1) for l in row)
                for row in _translated(original, aliases)]
    base, options, factors = _tables(inputs, physical, blocks, exterior)
    rows = []
    for ports, _, traces in factors:
        words = list(traces)
        if any(tuple((x&y)|(x&z)|(y&z) for x,y,z in zip(a,b,c)) not in traces
               for a,b,c in combinations(words, 3)):
            rows.append([[(w+1 if bit else -(w+1),) for w, bit in zip(ports, word)]
                         for word in words])
    if len(rows) != len(options):
        raise AssertionError("orientation and row tables disagree")
    return physical, expanded, aliases, base, factors, rows


def _relations(n, base, rows):
    domains = []
    for choices in rows:
        domain = [s for s, units in enumerate(choices) if _sat(n, base + units) is not None]
        if not domain:
            return None
        domains.append(domain)
    relations = [{} for _ in rows]
    for i, j in combinations(range(len(rows)), 2):
        ok = {(s, t) for s, t in product(domains[i], domains[j])
              if _sat(n, base + rows[i][s] + rows[j][t]) is not None}
        if not ok:
            return None
        if len(ok) < len(domains[i]) * len(domains[j]):
            relations[i][j] = ok
            relations[j][i] = {(t,s) for s,t in ok}
    return domains, relations


def _tree(order, parent, domains, relations):
    feasible = {}
    for i in reversed(order):
        children = [j for j in relations[i] if parent.get(j) == i]
        feasible[i] = [s for s in domains[i] if all(
            any((s,t) in relations[i][j] for t in feasible[j]) for j in children)]
    root = order[0]
    if not feasible[root]:
        return None
    chosen = {root: feasible[root][0]}
    for j in order[1:]:
        i = parent[j]
        chosen[j] = next(t for t in feasible[j] if (chosen[i],t) in relations[i][j])
    return chosen


def solve(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None,
          max_bad=None, max_search=None):
    """Return status, stats and original raw. max_search counts cyclic tuples.

    Projections of 2-CNF are 2-CNF. Inconsistent unit pins against a feasible
    base therefore contain an inconsistent singleton or pair. All compatible
    row selections integrate, including across disconnected components.
    Forest DP takes polynomial time. Sum the products of domain sizes over
    cyclic components for the fallback tuple bound. Space is polynomial.
    """
    gates = _net(inputs, gates)
    for cap in (max_bad, max_search):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("invalid cap")
    if output is not None:
        if type(output) is not int or not 0 <= output < inputs + len(gates):
            raise ValueError("invalid designated output")
        pins = tuple(pins) + ((output, 1),)
    original = _rows(inputs+len(gates), clauses, pins, equalities)
    physical, expanded, aliases, base, factors, rows = _prepare(inputs, gates, original)
    n = inputs + len(physical)
    stats = dict(bad=len(rows), forest_components=0, cyclic_components=0, searched=0)
    if max_bad is not None and len(rows) > max_bad:
        return "skip", stats, None
    if _sat(n, base) is None:
        return "unsat", stats, None
    pairwise = _relations(n, base, rows)
    if pairwise is None:
        return "unsat", stats, None
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
                return "unsat", stats, None
        else:
            stats["cyclic_components"] += 1
            for values in product(*(domains[i] for i in order)):
                if max_search is not None and stats["searched"] >= max_search:
                    return "skip", stats, None
                stats["searched"] += 1
                assignment = dict(zip(order, values))
                if all((assignment[i], assignment[j]) in relations[i][j] for i,j in edges):
                    break
            else:
                return "unsat", stats, None
        chosen.update(assignment)
    full = base.copy()
    for i, s in chosen.items():
        full.extend(rows[i][s])
    model = _sat(n, full)
    if model is None:
        raise AssertionError("joint unit pins violated binary-projection property")
    raw = model[:inputs]
    for ports, entries, traces in factors:
        choice = traces[tuple(model[w] for w in ports)]
        for w, bit in zip(entries, choice):
            if w < inputs:
                raw[w] = bit
    physical_wires = _replay(raw, physical)
    wires = _replay(raw, gates)
    if any(w != ((0 if v == -1 else physical_wires[expanded[v]]) ^ flip)
           for w, (v, flip) in zip(wires, aliases)):
        raise AssertionError("original signed wire replay failed")
    if any(not any(physical_wires[abs(l)-1] == (l>0) for l in row) for row in full):
        raise AssertionError("selected rows failed physical replay")
    if any(not any(wires[abs(l)-1] == (l>0) for l in row) for row in original):
        raise AssertionError("original exterior or output failed replay")
    return "sat", stats, tuple(raw)
