"""Minimum number of nonbijunctive contiguous two-input blocks in a NAND DAG."""

from corridor_nand import _net, _project, _rows, corridor_witness


def minimum_partition(inputs, gates, observed=()):
    """Return (minimum bad blocks, tuple of half-open gate-index intervals)."""
    gates = _net(inputs, gates)
    n = len(gates)
    wires = inputs + n
    observed = set(observed)
    if any(not isinstance(x, int) or not 0 <= x < wires for x in observed):
        raise ValueError("invalid observation")
    first = [n] * wires
    last = [-1] * wires
    for i, (a, b) in enumerate(gates):
        for x in (a, b):
            first[x] = min(first[x], i)
            last[x] = i

    cost = [n + 1] * (n + 1)
    cost[0] = 0
    parent = [-1] * (n + 1)
    for start in range(n):
        incoming = set()
        for j in range(start, n):
            incoming.update(x for x in gates[j] if x < inputs + start)
            if len(incoming) > 2:
                break
            stop = j + 1
            if cost[start] >= cost[stop]:
                continue
            entries = tuple(sorted(incoming))
            ports = [x for x in entries if x >= inputs or x in observed
                     or first[x] < start or last[x] >= stop]
            ports.extend(x for x in range(inputs + start, inputs + stop)
                         if x in observed or last[x] >= stop)
            _, bad = _project(inputs, gates, range(start, stop), tuple(ports), entries)
            score = cost[start] + int(bad)
            if score < cost[stop]:
                cost[stop] = score
                parent[stop] = start

    intervals = []
    stop = n
    while stop:
        start = parent[stop]
        intervals.append((start, stop))
        stop = start
    return cost[n], tuple(reversed(intervals))


def interval_witness(inputs, gates, *, clauses=(), pins=(), equalities=()):
    """Return (minimum bad blocks, partition, raw tuple or None).

    Gates use physical wire IDs, with gate i producing inputs+i. Clauses use
    DIMACS wire+1 literals, pins (wire, bit), equalities (a, b, xor target).
    """
    gates = tuple(tuple(gate) for gate in gates)
    clauses = tuple(tuple(clause) for clause in clauses)
    pins = tuple(tuple(pin) for pin in pins)
    equalities = tuple(tuple(eq) for eq in equalities)
    rows = _rows(inputs + len(gates), clauses, pins, equalities)
    observed = {abs(literal) - 1 for row in rows for literal in row}
    bad, intervals = minimum_partition(inputs, gates, observed)
    groups = tuple(range(start, stop) for start, stop in intervals)
    status, raw = corridor_witness(inputs, gates, groups, clauses=clauses, pins=pins,
                                   equalities=equalities, max_bad=bad)
    if status not in ("sat", "unsat"):
        raise AssertionError("optimal admissible interval partition was skipped")
    return bad, intervals, raw
