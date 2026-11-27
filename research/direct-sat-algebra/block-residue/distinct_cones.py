"""Globally optimal two-entry gate partition on tied-input-free NAND DAGs."""

from corridor_nand import _net, _rows, corridor_witness
from pair_optimizer import _Costs


def cone_groups(inputs, gates):
    """Return maximal two-entry cones on original gate IDs; ties return None."""
    gates = _net(inputs, gates)
    if any(a == b for a, b in gates):
        return None
    seeds = sorted({tuple(sorted(pair)) for pair in gates})
    cones = set()
    for pair in seeds:
        available = set(pair)
        cone = 0
        for i, (a, b) in enumerate(gates):
            if a in available and b in available:
                available.add(inputs+i)
                cone |= 1 << i
        cones.add(cone)
    maxima = []
    covered = 0
    for cone in sorted(cones, key=lambda c: (-c.bit_count(), c)):
        if any(cone & outer == cone for outer in maxima):
            continue
        if cone & covered:
            raise AssertionError("maximal distinct-operand cones overlap")
        maxima.append(cone)
        covered |= cone
    if covered != (1 << len(gates))-1:
        raise AssertionError("maximal cones do not cover the original gates")
    return tuple(sorted(tuple(i for i in range(len(gates)) if mask >> i & 1)
                        for mask in maxima))


def maximal_cone_partition(inputs, gates, observed=()):
    """Return (minimum bad blocks, gate groups), or None for tied operands.

    The first gate of every nonempty two-entry group must read both distinct
    entries. Saturation from that physical operand pair therefore contains
    the entire group. The maximal such cones form a disjoint cover. Merging
    any partition within one maximal cone costs at most the sum of its old
    costs: all-good pieces glue by join and projection of majority relations.
    """
    costs = _Costs(inputs, gates, observed)
    groups = cone_groups(inputs, costs.gates)
    if groups is None:
        return None
    scores = [costs.score(group) for group in groups]
    if None in scores:
        raise AssertionError("maximal cone has more than two incoming wires")
    total = sum(scores)
    costs.verify(groups, total)
    return total, groups


def distinct_cone_witness(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None):
    """Return (status,bad,groups,raw); output optionally designates a positive wire."""
    gates = _net(inputs, gates)
    wires = inputs + len(gates)
    clauses = tuple(tuple(c) for c in clauses)
    pins = tuple(tuple(p) for p in pins)
    equalities = tuple(tuple(eq) for eq in equalities)
    if output is not None:
        if type(output) is not int or not 0 <= output < wires:
            raise ValueError("invalid designated output wire")
        pins += ((output, 1),)
    rows = _rows(wires, clauses, pins, equalities)
    observed = {abs(l)-1 for row in rows for l in row}
    partition = maximal_cone_partition(inputs, gates, observed)
    if partition is None:
        return "skip", None, None, None
    bad, groups = partition
    status, raw = corridor_witness(inputs, gates, groups, clauses=clauses, pins=pins,
                                  equalities=equalities, max_bad=bad)
    if status not in ("sat", "unsat"):
        raise AssertionError("verified maximal cone partition was skipped")
    return status, bad, groups, raw
