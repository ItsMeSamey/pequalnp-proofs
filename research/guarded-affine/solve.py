"""Witness search for affine guarded decisions. Bit positions start at zero."""
from itertools import combinations


def holds(literals, assignment):
    return any(((mask & assignment).bit_count() & 1) ^ bias for mask, bias in literals)


def monomials(indices, degree):
    return [sum(1 << i for i in subset)
            for size in range(min(degree, len(indices)) + 1)
            for subset in combinations(indices, size)]


def representatives(assignments, masks):
    pivots = {}
    keep = []
    for x in assignments:
        row = sum(1 << j for j, m in enumerate(masks) if x & m == m)
        while row:
            j = row.bit_length() - 1
            if j not in pivots:
                pivots[j] = row
                keep.append(x)
                break
            row ^= pivots[j]
    return keep


def witness(guards, terminal, order, feedback=()):
    """Return a witness or None. Guard i is required if bit i is one.

    A literal (mask, bias) means parity(mask & assignment) xor bias.
    The order covers the variables outside the supplied feedback set.
    """
    n = len(guards)
    order, feedback = tuple(order), tuple(feedback)
    if sorted(order + feedback) != list(range(n)):
        raise ValueError("order and feedback must partition the variable indices")
    for clause in (*guards, *terminal):
        if any(mask < 0 or mask >= 1 << n or bias not in (0, 1) for mask, bias in clause):
            raise ValueError("invalid affine literal")
    known = sum(1 << i for i in feedback)
    for i in order:
        known |= 1 << i
        if any(mask & ~known for mask, _ in guards[i]):
            raise ValueError("a guard depends on a later decision")
    for fixed in range(1 << len(feedback)):
        chosen = [i for j, i in enumerate(feedback) if fixed & (1 << j)]
        tests = list(terminal) + [guards[i] for i in chosen]
        samples = [sum(1 << i for i in chosen)]
        prefix = []
        for i in order:
            ones = [x | (1 << i) for x in samples if holds(guards[i], x | (1 << i))]
            prefix.append(i)
            samples = representatives(samples + ones, monomials(prefix, len(tests)))
        for x in samples:
            if all(holds(c, x) for c in tests):
                return x
    return None
