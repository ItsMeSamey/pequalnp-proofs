"""Checked two-input NAND block projections with physical wire interfaces."""
from itertools import combinations, product


def _rows(n, clauses, pins, equalities):
    rows = [tuple(c) for c in clauses]
    if any(len(c) > 2 or any(type(l) is not int or not 1 <= abs(l) <= n for l in c)
           for c in rows):
        raise ValueError("invalid exterior clause")
    for x, bit in pins:
        if not 0 <= x < n or bit not in (0, 1):
            raise ValueError("invalid wire pin")
        rows.append(((x+1) if bit else -(x+1),))
    for x, y, parity in equalities:
        if not (0 <= x < n and 0 <= y < n and parity in (0, 1)):
            raise ValueError("invalid signed equality")
        a, b = x+1, (y+1) * (-1 if parity else 1)
        rows.extend(((-a, b), (a, -b)))
    return rows


def _net(inputs, gates):
    gates = tuple(tuple(g) for g in gates)
    if type(inputs) is not int or inputs < 0:
        raise ValueError("invalid primary count")
    for i, (a, b) in enumerate(gates):
        if not (type(a) is int and type(b) is int and 0 <= a < inputs+i and 0 <= b < inputs+i):
            raise ValueError("invalid topological NAND")
    return gates


def _replay(raw, gates):
    w = list(raw)
    for a, b in gates:
        w.append(1 ^ (w[a] & w[b]))
    return w


def _sat(n, rows):
    graph = [[] for _ in range(2*n)]
    reverse = [[] for _ in graph]
    for row in rows:
        if not row:
            return None
        a, b = (2*(abs(l)-1) + (l < 0) for l in (row[0], row[-1]))
        for x, y in ((a^1, b), (b^1, a)):
            graph[x].append(y)
            reverse[y].append(x)
    order = []
    seen = set()
    for x in range(2*n):
        if x in seen:
            continue
        seen.add(x)
        stack = [(x, iter(graph[x]))]
        while stack:
            v, adj = stack[-1]
            u = next(adj, None)
            if u is None:
                order.append(v)
                stack.pop()
            elif u not in seen:
                seen.add(u)
                stack.append((u, iter(graph[u])))
    comp = [-1]*(2*n)
    for k, x in enumerate(reversed(order)):
        if comp[x] >= 0:
            continue
        stack = [x]
        comp[x] = k
        while stack:
            for u in reverse[stack.pop()]:
                if comp[u] < 0:
                    comp[u] = k
                    stack.append(u)
    if any(comp[i] == comp[i+1] for i in range(0, 2*n, 2)):
        return None
    return [int(comp[i] > comp[i+1]) for i in range(0, 2*n, 2)]


def _hull(visible, words):
    rows = []
    representatives = {}
    kept = []
    for i, x in enumerate(visible):
        pattern = tuple(w[i] for w in words)
        if pattern in representatives:
            y = representatives[pattern]
            rows.extend(((-(x+1), y+1), (x+1, -(y+1))))
        else:
            representatives[pattern] = x
            kept.append(i)
    visible = [visible[i] for i in kept]
    words = [tuple(w[i] for i in kept) for w in words]
    for i, x in enumerate(visible):
        for a in (0, 1):
            if not any(w[i] == a for w in words):
                rows.append(((x+1) * (1-2*a),))
        for j in range(i):
            y = visible[j]
            present = {(w[i], w[j]) for w in words}
            for a, b in product((0, 1), repeat=2):
                if (a, b) not in present:
                    rows.append(((x+1)*(1-2*a), (y+1)*(1-2*b)))
    return rows


def _project(inputs, gates, ids, ports, entries):
    traces = {}
    for choice in product((0, 1), repeat=len(entries)):
        local = dict(zip(entries, choice))
        for i in ids:
            a, b = gates[i]
            local[inputs+i] = 1 ^ (local[a] & local[b])
        traces.setdefault(tuple(local[v] for v in ports), choice)
    bad = any(tuple((x & y) | (x & z) | (y & z) for x, y, z in zip(a,b,c))
              not in traces for a,b,c in combinations(traces, 3))
    return traces, bad


def corridor_witness(inputs, gates, groups, *, clauses=(), pins=(), equalities=(), max_bad=0):
    """Solve gated CSP on indexed physical wires. Uncovered gates must be NOTs.

    Groups contain zero-based gate indices. Each may read at most two distinct
    external physical wires. DIMACS literal abs(l) denotes wire abs(l)-1.
    max_bad limits non-majority groups; an exceeded budget yields skip.
    """
    gates = _net(inputs, gates)
    n = inputs + len(gates)
    rows = _rows(n, clauses, pins, equalities)
    if type(max_bad) is not int or max_bad < 0:
        raise ValueError("invalid branch budget")
    groups = [tuple(g) for g in groups]
    owner = [-1]*len(gates)
    for k, group in enumerate(groups):
        for i in group:
            if type(i) is not int or not 0 <= i < len(gates) or owner[i] != -1:
                return "skip", None
            owner[i] = k
    for i, k in enumerate(owner):
        if k < 0:
            a, b = gates[i]
            if a != b:
                return "skip", None
            rows.extend(_rows(n, (), (), ((a, inputs+i, 1),)))
    observed = {abs(l)-1 for row in rows for l in row}
    readers = [set() for _ in range(n)]
    for i, (a, b) in enumerate(gates):
        readers[a].add(owner[i])
        readers[b].add(owner[i])
    factors = []
    alternatives = []
    for k, group in enumerate(groups):
        ids = sorted(group)
        outs = {inputs+i for i in ids}
        entries = sorted({v for i in ids for v in gates[i]} - outs)
        if len(entries) > 2:
            return "skip", None
        ports = sorted(v for v in outs.union(entries)
                       if v in observed or readers[v] - {k}
                       or (v in entries and v >= inputs))
        traces, bad = _project(inputs, gates, ids, ports, entries)
        words = list(traces)
        if bad:
            alternatives.append((_hull(ports, words[:2]), _hull(ports, words[2:])))
            if len(alternatives) > max_bad:
                return "skip", None
        else:
            rows.extend(_hull(ports, words))
        factors.append((ports, traces, entries))
    for sides in product((0, 1), repeat=len(alternatives)):
        combined = rows.copy()
        for pair, side in zip(alternatives, sides):
            combined.extend(pair[side])
        values = _sat(n, combined)
        if values is None:
            continue
        raw = values[:inputs]
        for ports, traces, entries in factors:
            choice = traces[tuple(values[v] for v in ports)]
            for v, b in zip(entries, choice):
                if v < inputs:
                    raw[v] = b
        wires = _replay(raw, gates)
        if not all(any(wires[abs(l)-1] == (l > 0) for l in row) for row in combined):
            raise AssertionError("physical NAND/exterior witness replay failed")
        return "sat", tuple(raw)
    return "unsat", None


def compile_objective(inputs, gates, *, clauses=(), pins=(), equalities=()):
    """Append the NAND conjunction of the exterior; return (inputs,gates,out)."""
    gates = list(_net(inputs, gates))
    n = inputs + len(gates)
    rows = _rows(n, clauses, pins, equalities)
    if not n:
        raise ValueError("NAND objective needs a physical wire for constants")

    def nand(a, b):
        gates.append((a, b))
        return inputs+len(gates)-1

    def neg(w):
        return nand(w, w)

    def literal(l):
        return abs(l)-1 if l > 0 else neg(abs(l)-1)

    def one():
        return nand(0, neg(0))

    parts = []
    for row in rows:
        if not row:
            parts.append(neg(one()))
        elif len(row) == 1:
            parts.append(literal(row[0]))
        else:
            parts.append(nand(literal(-row[0]), literal(-row[1])))
    output = parts[0] if parts else one()
    for part in parts[1:]:
        output = neg(nand(output, part))
    return inputs, tuple(gates), output


def nand_cnf(source):
    """Return full gate CNF and the designated positive output unit in DIMACS."""
    inputs, gates, output = source
    gates = _net(inputs, gates)
    if not 0 <= output < inputs + len(gates):
        raise ValueError("invalid output wire")
    rows = []
    for i, (a, b) in enumerate(gates):
        x, y, z = a+1, b+1, inputs+i+1
        rows.extend(((-x,-y,-z), (x,z), (y,z)))
    rows.append((output+1,))
    return tuple(rows)


def solve_compiled(source, base_gate_count, groups, *, clauses=(), pins=(), equalities=(),
                   max_bad=0):
    """Recognize the canonical objective suffix; replay the designated output."""
    inputs, gates, output = source
    gates = _net(inputs, gates)
    if type(base_gate_count) is not int or not 0 <= base_gate_count <= len(gates):
        return "skip", None
    if not inputs:
        return "skip", None
    opts = dict(clauses=tuple(tuple(c) for c in clauses), pins=tuple(pins),
                equalities=tuple(equalities))
    base = gates[:base_gate_count]
    if compile_objective(inputs, base, **opts) != (inputs, gates, output):
        return "skip", None
    status, raw = corridor_witness(inputs, base, groups, max_bad=max_bad, **opts)
    if status == "sat":
        wires = _replay(raw, gates)
        if not wires[output] or not all(
            any(wires[abs(l)-1] == (l > 0) for l in row)
            for row in nand_cnf((inputs, gates, output))
        ):
            raise AssertionError("designated output or original NAND CNF replay failed")
    return status, raw
