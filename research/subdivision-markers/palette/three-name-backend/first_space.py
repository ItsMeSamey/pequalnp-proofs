"""First-space recovery from indexed private keys and two-bit tags."""
from exact_line import exact_line, pivots
from graphic import is_graphic


def scalar_relation(keys, tags, scalar, *, forced=(), graphic=is_graphic):
    if len(keys) != len(tags) or any(k < 0 for k in keys) or any(t not in range(4) for t in tags):
        raise ValueError("expected private keys and two-bit tags")
    if not 0 <= scalar < 1 << len(keys):
        raise ValueError("expected indexed binary scalar")
    cols = [(k << 3) | (t << 1) | (scalar >> i & 1)
            for i, (k, t) in enumerate(zip(keys, tags))]
    sites = exact_line(cols, 1, 2, 4, forced=forced, graphic=graphic)
    if sites is None:
        return None
    table = {}
    for i in sites:
        value, mask = cols[i], 1 << i
        while value:
            bit = value.bit_length() - 1
            if bit not in table:
                table[bit] = value, mask
                break
            row, coeff = table[bit]
            value ^= row
            mask ^= coeff
    relation = table[0][1]
    accumulated = 0
    for i in sites:
        if relation >> i & 1:
            accumulated ^= cols[i]
    if accumulated != 1 or relation & ~sum(1 << i for i in sites):
        raise AssertionError("invalid original scalar-odd private relation")
    return relation, sites


def annihilator(rows, dimension):
    basis = pivots(rows)
    for free in range(dimension):
        if free in basis:
            continue
        test = 1 << free
        for bit in sorted(basis):
            if (basis[bit] & test).bit_count() & 1:
                test |= 1 << bit
        yield test


def first_space(keys, tags, *, graphic=is_graphic):
    """Independent masks of actually realizable relations spanning L."""
    if len(keys) != len(tags):
        raise ValueError("expected equally many keys and tags")
    rows = []
    n = len(keys)
    while True:
        for scalar in annihilator(rows, n):
            found = scalar_relation(keys, tags, scalar, graphic=graphic)
            if found is not None:
                rows.append(found[0])
                break
        else:
            return tuple(rows)
