"""Best single admissible merge of whole blocks in a supplied NAND partition."""

from itertools import chain, combinations

from corridor_nand import _rows, corridor_witness
from pair_optimizer import _Costs, _singletons


def _seed(costs, supplied):
    groups = _singletons(costs) if supplied is None else tuple(tuple(g) for g in supplied)
    owner = [-1] * len(costs.gates)
    canon = []
    for b, group in enumerate(groups):
        if not group:
            raise ValueError("empty seed block")
        for i in group:
            if type(i) is not int or not 0 <= i < len(owner) or owner[i] >= 0:
                raise ValueError("invalid or repeated seed gate ID")
            owner[i] = b
        canon.append(tuple(sorted(group)))
    if -1 in owner:
        raise ValueError("incomplete seed coverage")
    scores = [costs.score(group) for group in canon]
    if None in scores:
        raise ValueError("seed block has more than two incoming wires")
    return tuple(canon), owner, scores


def _dependencies(costs, groups, owner):
    """Build raw-entry and producer-to-consumer links, labelled by physical wire."""
    raw = [set() for _ in groups]
    dependencies = [set() for _ in groups]
    candidates = set()
    for i, gate in enumerate(costs.gates):
        b = owner[i]
        for v in gate:
            if v < costs.inputs:
                raw[b].add(v)
            else:
                producer = owner[v - costs.inputs]
                if producer == b:
                    continue
                dependencies[producer].add((v, b))
            candidates.add(v)
    return raw, dependencies, sorted(candidates)


def _closure(raw, dependencies, ports):
    removed = [not entries.issubset(ports) for entries in raw]
    pending = [i for i, gone in enumerate(removed) if gone]
    while pending:
        i = pending.pop()
        for wire, other in dependencies[i]:
            if wire not in ports and not removed[other]:
                removed[other] = True
                pending.append(other)
    return tuple(i for i, gone in enumerate(removed) if not gone)


def maximum_cone_partition(inputs, gates, observed=(), *, seed=None):
    """Return (minimum bad blocks, groups) over at most one arbitrary seed merge.

    For each possible incoming port set P of size at most two, deletion finds
    the unique largest union whose incoming wires lie in P. Extending a feasible
    union by remaining seed blocks cannot decrease savings: if any added block
    costs one it pays for any cost increase (at most one); otherwise a previously
    good union joined with good blocks and projected stays majority closed.
    Enumerating P therefore suffices even for noncontiguous seed blocks.
    """
    costs = _Costs(inputs, gates, observed)
    groups, owner, scores = _seed(costs, seed)
    raw, dependencies, candidates = _dependencies(costs, groups, owner)
    best_gain = 0
    chosen = ()
    for port_tuple in chain(((),), combinations(candidates, 1), combinations(candidates, 2)):
        union = _closure(raw, dependencies, set(port_tuple))
        if len(union) < 2:
            continue
        old_cost = sum(scores[b] for b in union)
        if old_cost <= best_gain:
            continue
        ids = tuple(sorted(i for b in union for i in groups[b]))
        merged_cost = costs.score(ids)
        if merged_cost is None:
            raise AssertionError("closure has excess physical entries")
        gain = old_cost - merged_cost
        if gain > best_gain:
            best_gain = gain
            chosen = union
    if chosen:
        merged = tuple(sorted(i for b in chosen for i in groups[b]))
        used = set(chosen)
        groups = tuple(sorted([merged] + [g for b, g in enumerate(groups) if b not in used]))
    total = sum(scores) - best_gain
    costs.verify(groups, total)
    return total, groups


def cone_witness(inputs, gates, *, clauses=(), pins=(), equalities=(), seed=None):
    """Solve the original gated CSP with the selected maximum-cone partition."""
    gates = tuple(tuple(g) for g in gates)
    clauses = tuple(tuple(c) for c in clauses)
    pins = tuple(tuple(p) for p in pins)
    equalities = tuple(tuple(eq) for eq in equalities)
    rows = _rows(inputs + len(gates), clauses, pins, equalities)
    observed = {abs(l)-1 for row in rows for l in row}
    bad, groups = maximum_cone_partition(inputs, gates, observed, seed=seed)
    status, raw = corridor_witness(inputs, gates, groups, clauses=clauses, pins=pins,
                                  equalities=equalities, max_bad=bad)
    if status not in ("sat", "unsat"):
        raise AssertionError("verified maximum cone partition was skipped")
    return bad, groups, raw
