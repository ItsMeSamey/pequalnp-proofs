"""Signed alias normalization and optimal two-entry blocks on that representation."""
from corridor_nand import _net, _replay, _rows, corridor_witness
from distinct_cones import cone_groups
from pair_optimizer import _Costs


def normalize(inputs, gates):
    """Return signed gates and (base, flip) for each original wire; -1 is zero."""
    gates = _net(inputs, gates)
    aliases = [(i, 0) for i in range(inputs)]
    retained = []
    for a, b in gates:
        left, right = aliases[a], aliases[b]
        if left == (-1, 0) or right == (-1, 0):
            result = (-1, 1)
        elif left == (-1, 1) or left == right:
            result = right[0], 1 ^ right[1]
        elif right == (-1, 1):
            result = left[0], 1 ^ left[1]
        elif left[0] == right[0]:
            result = (-1, 1)
        else:
            result = inputs + len(retained), 0
            retained.append((left, right))
        aliases.append(result)
    return tuple(retained), tuple(aliases)


def _translated(rows, aliases):
    reduced = []
    for row in rows:
        literals = set()
        for literal in row:
            base, flip = aliases[abs(literal)-1]
            negative = flip ^ (literal < 0)
            if base == -1:
                if negative:
                    break
                continue
            value = -(base+1) if negative else base+1
            if -value in literals:
                break
            literals.add(value)
        else:
            reduced.append(tuple(sorted(literals)))
    return tuple(reduced)


def _materialize(inputs, retained, groups):
    """Materialized tied NANDs have just one reader, in their owner's block."""
    gates = []
    expanded = list(range(inputs))
    pieces = []
    for operands in retained:
        start = len(gates)
        reads = []
        for base, flip in operands:
            wire = expanded[base]
            if flip:
                gates.append((wire, wire))
                wire = inputs + len(gates) - 1
            reads.append(wire)
        gates.append(tuple(reads))
        expanded.append(inputs + len(gates) - 1)
        pieces.append(tuple(range(start, len(gates))))
    blocks = tuple(tuple(sorted(i for j in group for i in pieces[j])) for group in groups)
    return tuple(gates), tuple(expanded), blocks


def solve(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None):
    """Return status, normalized optimal cost, normalized groups, original raw."""
    gates = _net(inputs, gates)
    if output is not None:
        if type(output) is not int or not 0 <= output < inputs + len(gates):
            raise ValueError("invalid designated original output")
        pins = tuple(pins) + ((output, 1),)
    original_rows = _rows(inputs + len(gates), clauses, pins, equalities)
    retained, aliases = normalize(inputs, gates)
    rows = _translated(original_rows, aliases)
    topology = tuple((u[0], v[0]) for u, v in retained)
    groups = cone_groups(inputs, topology)
    if groups is None:
        raise AssertionError("normalization left equal base operands")
    physical, expanded, blocks = _materialize(inputs, retained, groups)
    mapped = tuple(tuple((expanded[abs(l)-1]+1)*(1 if l>0 else -1) for l in row)
                   for row in rows)
    observed = {abs(l)-1 for row in mapped for l in row}
    costs = _Costs(inputs, physical, observed)
    scores = [costs.score(block) for block in blocks]
    if None in scores:
        raise AssertionError("private materialization enlarged block boundary")
    bad = sum(scores)
    status, raw = corridor_witness(inputs, physical, blocks, clauses=mapped, max_bad=bad)
    if status == "sat":
        original = _replay(raw, gates)
        normalized = _replay(raw, physical)
        for value, (base, flip) in zip(original, aliases):
            expected = (0 if base == -1 else normalized[expanded[base]]) ^ flip
            if value != expected:
                raise AssertionError("original and normalized wires differ")
        if any(not any(original[abs(l)-1] == (l>0) for l in row) for row in original_rows):
            raise AssertionError("original exterior replay failed")
    elif status != "unsat":
        raise AssertionError("verified normalized partition skipped")
    return status, bad, groups, raw
