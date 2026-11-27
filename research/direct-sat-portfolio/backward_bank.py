"""Exact original-circuit counting and witness transfer on affine history quotients."""
from functools import lru_cache


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def reduce_vector(vector, basis):
    for pivot in sorted(basis, reverse=True):
        if vector >> pivot & 1:
            vector ^= basis[pivot]
    return vector


def independent(rows):
    basis = {}
    selected = []
    for row in rows:
        reduced = reduce_vector(row, basis)
        if reduced:
            basis[reduced.bit_length() - 1] = reduced
            selected.append(row)
    return tuple(selected)


def evaluate(rows, assignment):
    return sum(((row & assignment).bit_count() % 2) << i for i, row in enumerate(rows))


def ranges(size, width):
    return [(i, min(size, i + width)) for i in range(0, size, width)] or [(0, 0)]


def plan(n, gates, output, width):
    blocks = ranges(len(gates), width)
    raw_mask = (1 << (n + 1)) - 2
    used = 0
    history_mask = 0
    metadata = []
    for i, (lo, hi) in enumerate(blocks):
        operands = tuple(row for pair in gates[lo:hi] for row in pair)
        reads = output if i == len(blocks) - 1 else 0
        for row in operands:
            reads |= row
        fresh = reads & raw_mask & ~used
        metadata.append((lo, hi, operands, fresh, history_mask))
        used |= fresh
        history_mask = used | (((1 << hi) - 1) << (n + 1))
    outgoing = (output & ~1,)
    steps = []
    total_work = 0
    for lo, hi, operands, fresh, past in reversed(metadata):
        rows = operands + outgoing
        columns = {}
        # The height of a column is the current local observations plus the next sketch.
        for index, row in enumerate(rows):
            for variable in positions(row & (fresh | past)):
                columns[variable] = columns.get(variable, 0) | (1 << index)
        basis = {}
        fresh_generators = []
        for variable in positions(fresh):
            reduced = reduce_vector(columns.get(variable, 0), basis)
            if reduced:
                basis[reduced.bit_length() - 1] = reduced
                fresh_generators.append(1 << variable)
        # Quotient the past columns by the fresh column span, then select a row basis.
        history_rows = [0] * len(rows)
        for variable, column in columns.items():
            if past >> variable & 1:
                for coordinate in positions(reduce_vector(column, basis)):
                    history_rows[coordinate] |= 1 << variable
        incoming = independent(history_rows)
        rank = len(fresh_generators)
        work = 1 << (len(incoming) + rank)
        total_work += work
        steps.append((lo, hi, outgoing, tuple(fresh_generators),
                      fresh.bit_count() - rank, len(incoming), work))
        outgoing = incoming
    return total_work, tuple(reversed(steps)), n - used.bit_count(), width


@lru_cache(maxsize=2)
def best_plan(n, gates, output):
    widths = sorted({min(max(len(gates), 1), width) for width in (1, 2, 4)})
    return min((plan(n, gates, output, w) for w in widths), key=lambda result: result[0])


def estimate(n, gates, output):
    return best_plan(n, tuple(gates), output)[0]


def solve(n, gates, output, *, budget):
    gates = tuple(gates)
    cap, steps, unused, width = best_plan(n, gates, output)
    cost = {'metric': 'candidate_bank_transitions', 'bound': cap, 'bank_width': width,
            'incoming_ranks': [s[5] for s in steps],
            'fresh_ranks': [len(s[3]) for s in steps], 'transitions': 0}
    if cap > budget:
        return {'status': 'skip', 'cost': cost}
    # One fully realized raw/gate history plus the exact multiplicity for each key.
    states = {0: (1, 1)}
    for lo, hi, out_rows, generators, nullity, _, _ in steps:
        new_states = {}
        for multiplicity, history in states.values():
            fresh = 0
            for index in range(1 << len(generators)):
                if index:
                    fresh ^= generators[(index & -index).bit_length() - 1]
                assignment = history | fresh
                for j in range(lo, hi):
                    a, b = gates[j]
                    bit = (a & assignment).bit_count() & (b & assignment).bit_count() & 1
                    assignment |= bit << (n + 1 + j)
                key = evaluate(out_rows, assignment)
                mass = multiplicity << nullity
                if key in new_states:
                    old, witness = new_states[key]
                    new_states[key] = (old + mass, witness)
                else:
                    new_states[key] = (mass, assignment)
                cost['transitions'] += 1
        states = new_states
    accepted = states.get(1 ^ (output & 1))
    if accepted is None:
        cost['accept_count'] = 0
        return {'status':'unsat', 'cost':cost}
    count, assignment = accepted
    witness = (assignment >> 1) & ((1 << n) - 1)
    replay = 1 | (witness << 1)
    for j, (a, b) in enumerate(gates):
        bit = (a & replay).bit_count() & (b & replay).bit_count() & 1
        replay |= bit << (n + 1 + j)
    if not ((output & replay).bit_count() & 1):
        raise AssertionError('bank witness failed original-circuit replay')
    cost['accept_count'] = count << unused
    return {'status':'sat', 'witness':witness, 'cost':cost}
