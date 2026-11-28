"""Certified order charts for interactions between promoted NAND rows."""
from itertools import combinations, product
from corridor_nand import _hull, _net, _replay, _rows, _sat
from promoted_row_csp import _promote
from row_csp import _prepare, _relations


def _orders(domain, mode):
    first = tuple(sorted(domain))
    if mode == "min":
        return first, first[::-1]
    if len(first) >= 3:
        return first, (first[1], first[0]) + first[2:]
    return first, first


def _closed(relation, left, right, mode):
    pos = [{v:k for k,v in enumerate(order)} for order in (left, right)]
    arity = 2 if mode == "min" else 3
    # Repeated tuples automatically satisfy min and median closure.
    for rows in combinations(relation, arity):
        value = tuple(sorted(col, key=rank.__getitem__)[arity-2]
                      for col, rank in zip(zip(*rows), pos))
        if value not in relation:
            return False
    return True


def _chart(domains, relations, mode):
    orders = [_orders(domain, mode) for domain in domains]
    banned = []
    for i, neighbors in enumerate(relations):
        for j, relation in neighbors.items():
            if j <= i:
                continue
            for a,b in product((0,1), repeat=2):
                if not _closed(relation, orders[i][a], orders[j][b], mode):
                    banned.append(((i+1)*(1-2*a), (j+1)*(1-2*b)))
    bits = _sat(len(domains), banned)
    if bits is None:
        return None
    return [pair[b] for pair,b in zip(orders,bits)]


def _least(orders, relations):
    remaining = [list(order) for order in orders]
    changed = True
    while changed:
        changed = False
        for i, neighbors in enumerate(relations):
            keep = [a for a in remaining[i] if all(
                any((a,b) in relation for b in remaining[j]) for j, relation in neighbors.items())]
            if not keep:
                return None
            if len(keep) != len(remaining[i]):
                remaining[i] = keep
                changed = True
    return {i: values[0] for i, values in enumerate(remaining)}


def _median(orders, relations):
    ids = []
    enc = []
    n = 0
    clauses = []
    for order in orders:
        thresholds = tuple(range(n, n+len(order)-1))
        n += len(thresholds)
        ids.append(thresholds)
        enc.append({v: tuple(int(j < p) for j in range(len(thresholds)))
                    for p,v in enumerate(order)})
        clauses.extend((-(y+1), x+1) for x,y in zip(thresholds,thresholds[1:]))
    for i, neighbors in enumerate(relations):
        for j, rel in neighbors.items():
            if i < j:
                words = [enc[i][a]+enc[j][b] for a,b in rel]
                clauses.extend(_hull(ids[i]+ids[j], words))
    model = _sat(n, clauses)
    if model is None:
        return None
    return {i: order[sum(model[w] for w in ids[i])] for i,order in enumerate(orders)}


def ordered_assignment(domains, relations, mode="auto"):
    """Find a certified ordered chart or skip if the candidates do not certify one.

    Domains contain up to four distinct nonnegative row IDs. Supply symmetric
    adjacency dictionaries of allowed directed pairs; omitted edges are free.
    """
    if mode not in ("auto","min","median"):
        raise ValueError("invalid chart mode")
    domains = [tuple(d) for d in domains]
    n = len(domains)
    if len(relations) != n or any(len(d) > 4 or len(d) != len(set(d))
                                  or any(type(v) is not int or v < 0 for v in d)
                                  for d in domains):
        raise ValueError("invalid row domains")
    for i, neighbors in enumerate(relations):
        for j, rel in neighbors.items():
            if type(j) is not int or not 0 <= j < n or j == i:
                raise ValueError("invalid relation endpoints")
            if any(a not in domains[i] or b not in domains[j] for a,b in rel):
                raise ValueError("relation leaves declared domains")
            if i not in relations[j] or {(b,a) for a,b in rel} != set(relations[j][i]):
                raise ValueError("asymmetric adjacency")
    if any(not d for d in domains) or any(not rel for adj in relations for rel in adj.values()):
        return "unsat", None, None
    for kind in (("min","median") if mode == "auto" else (mode,)):
        chart = _chart(domains, relations, kind)
        if chart is None:
            continue
        values = _least(chart, relations) if kind == "min" else _median(chart, relations)
        if values is None:
            return "unsat", kind, None
        if any((values[i], values[j]) not in rel for i, adj in enumerate(relations)
               for j, rel in adj.items()):
            raise AssertionError("chart decoding violated original row relation")
        return "sat", kind, values
    return "skip", None, None


def solve(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None,
          mode="auto", max_bad=None):
    """Check min/median charts on the original NAND problem after row promotion."""
    gates = _net(inputs, gates)
    if mode not in ("auto", "min", "median"):
        raise ValueError("invalid chart mode")
    if max_bad is not None and (type(max_bad) is not int or max_bad < 0):
        raise ValueError("invalid cap")
    if output is not None:
        if type(output) is not int or not 0 <= output < inputs+len(gates):
            raise ValueError("invalid wire")
        pins = tuple(pins) + ((output, 1),)
    original = _rows(inputs+len(gates), clauses, pins, equalities)
    physical, expanded, aliases, base, factors, tables = _prepare(inputs, gates, original)
    n = inputs + len(physical)
    stats = dict(initial_bad=len(tables), bad=len(tables), promoted=0, pruned=0, method=None)
    rows = _promote(n, base, tables, stats)
    if rows is None:
        return "unsat", stats, None
    if max_bad is not None and len(rows) > max_bad:
        return "skip", stats, None
    pairwise = _relations(n, base, rows)
    if pairwise is None:
        return "unsat", stats, None
    status, kind, chosen = ordered_assignment(*pairwise, mode=mode)
    stats["method"] = kind
    if status != "sat":
        return status, stats, None
    full = base.copy()
    for i, value in chosen.items():
        full.extend(rows[i][value])
    model = _sat(n, full)
    if model is None:
        raise AssertionError("compatible ordered rows failed to integrate")
    raw = model[:inputs]
    for ports, entries, traces in factors:
        word = traces[tuple(model[w] for w in ports)]
        for w, bit in zip(entries, word):
            if w < inputs:
                raw[w] = bit
    material = _replay(raw, physical)
    wires = _replay(raw, gates)
    if any(w != ((0 if v == -1 else material[expanded[v]]) ^ flip)
           for w, (v, flip) in zip(wires, aliases)):
        raise AssertionError("original wire alias failed replay")
    if any(not any(material[abs(l)-1] == (l > 0) for l in row) for row in full):
        raise AssertionError("row model failed physical replay")
    if any(not any(wires[abs(l)-1] == (l > 0) for l in row) for row in original):
        raise AssertionError("original exterior or output failed replay")
    return "sat", stats, tuple(raw)
