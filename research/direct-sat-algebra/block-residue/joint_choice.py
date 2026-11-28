"""Learn binary conflicts between signed NAND cone orientation choices."""

from itertools import combinations, product

from corridor_nand import _hull, _net, _project, _replay, _rows, _sat
from distinct_cones import cone_groups
from signed_cone_nand import _materialize, _translated, normalize


def _tables(inputs, gates, blocks, exterior):
    """Every block contributes its binary hull to the common relaxation."""
    base = list(exterior)
    observed = {abs(l)-1 for row in exterior for l in row}
    readers = [set() for _ in range(inputs + len(gates))]
    for k, ids in enumerate(blocks):
        for i in ids:
            for x in gates[i]:
                readers[x].add(k)
    factors = []
    alternatives = []
    for k, ids in enumerate(blocks):
        outs = {inputs+i for i in ids}
        entries = sorted({w for i in ids for w in gates[i]} - outs)
        if len(entries) > 2:
            raise AssertionError("materialized block has excess entrances")
        ports = sorted(w for w in outs.union(entries)
                       if w in observed or readers[w] - {k}
                       or (w in entries and w >= inputs))
        traces, bad = _project(inputs, gates, ids, ports, entries)
        words = list(traces)
        base.extend(_hull(ports, words))
        if bad:
            alternatives.append((_hull(ports, words[:2]), _hull(ports, words[2:])))
        factors.append((ports, entries, traces))
    return base, alternatives, factors


def _learn(n, base, options):
    if _sat(n, base) is None:
        return ((),)
    rows = []
    allowed = []
    for i, pair in enumerate(options):
        sides = []
        for s in (0, 1):
            if _sat(n, base + pair[s]) is None:
                rows.append(((i+1) * (1-2*s),))
            else:
                sides.append(s)
        allowed.append(sides)
    for i, j in combinations(range(len(options)), 2):
        for s, t in product(allowed[i], allowed[j]):
            if _sat(n, base + options[i][s] + options[j][t]) is None:
                rows.append(((i+1)*(1-2*s), (j+1)*(1-2*t)))
    return tuple(rows)


def _models(n, rows):
    """Polynomial-delay depth-first enumeration by prefix extension tests."""
    stack = [()]
    while stack:
        prefix = stack.pop()
        units = tuple(((i+1 if bit else -(i+1)),) for i, bit in enumerate(prefix))
        if _sat(n, rows + units) is None:
            continue
        if len(prefix) == n:
            yield prefix
        else:
            stack.extend((prefix + (1,), prefix + (0,)))


def solve(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None,
          max_bad=None, max_models=None):
    """Return status, statistics and a raw witness for an original NAND circuit.

    selector_clauses uses one-based DIMACS selector IDs in bad cone order.
    tested counts complete physical two-SAT checks. A cap can yield skip.
    With unlimited caps, time is polynomial in input size times (1+M) for
    M models of the learned selector formula; auxiliary space is polynomial.
    """
    gates = _net(inputs, gates)
    for cap in (max_bad, max_models):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("invalid nonnegative cap")
    if output is not None:
        if type(output) is not int or not 0 <= output < inputs+len(gates):
            raise ValueError("invalid designated output wire")
        pins = tuple(pins) + ((output, 1),)
    original = _rows(inputs+len(gates), clauses, pins, equalities)
    retained, aliases = normalize(inputs, gates)
    groups = cone_groups(inputs, [(a[0], b[0]) for a, b in retained])
    if groups is None:
        raise AssertionError("signed normalization left tied base operands")
    physical, expanded, blocks = _materialize(inputs, retained, groups)
    exterior = [tuple((expanded[abs(l)-1]+1)*(1 if l>0 else -1) for l in row)
                for row in _translated(original, aliases)]
    base, options, factors = _tables(inputs, physical, blocks, exterior)
    b = len(options)
    stats = dict(bad=b, selector_clauses=(), tested=0)
    if max_bad is not None and b > max_bad:
        return "skip", stats, None
    n = inputs + len(physical)
    stats["selector_clauses"] = _learn(n, base, options)
    for orientation in _models(b, stats["selector_clauses"]):
        if max_models is not None and stats["tested"] >= max_models:
            return "skip", stats, None
        stats["tested"] += 1
        full = base.copy()
        for pair, side in zip(options, orientation):
            full.extend(pair[side])
        values = _sat(n, full)
        if values is None:
            continue
        raw = values[:inputs]
        for ports, entries, traces in factors:
            choice = traces[tuple(values[w] for w in ports)]
            for w, bit in zip(entries, choice):
                if w < inputs:
                    raw[w] = bit
        physical_wires = _replay(raw, physical)
        if any(not any(physical_wires[abs(l)-1] == (l>0) for l in row) for row in full):
            raise AssertionError("projected witness failed physical replay")
        wires = _replay(raw, gates)
        if any(w != ((0 if v == -1 else physical_wires[expanded[v]]) ^ flip)
               for w, (v, flip) in zip(wires, aliases)):
            raise AssertionError("original wire aliases failed replay")
        if any(not any(wires[abs(l)-1] == (l>0) for l in row) for row in original):
            raise AssertionError("original exterior or output failed replay")
        return "sat", stats, tuple(raw)
    return "unsat", stats, None
