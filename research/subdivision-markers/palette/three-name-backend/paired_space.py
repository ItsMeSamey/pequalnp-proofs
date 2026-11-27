"""Paired W via the pinned, single-exponential first-rank branch."""
from first_space import annihilator, first_space, scalar_relation
from graphic import is_graphic


def wedge(u, v, n):
    value = 0
    for j in range(n):
        block = (u if v >> j & 1 else 0) ^ (v if u >> j & 1 else 0)
        value |= (block & ((1 << j) - 1)) << (j * (j - 1) // 2)
    return value


def separate(keys, tags, first_rows, form, *, graphic):
    n = len(keys)
    u = 0
    for word in range(1, 1 << len(first_rows)):
        # Consecutive Gray words differ at the least significant set bit of word.
        u ^= first_rows[(word & -word).bit_length() - 1]
        scalar = sum((((form & wedge(u, 1 << i, n)).bit_count() & 1) << i) for i in range(n))
        if not scalar:
            continue
        pins = tuple(i for i in range(n) if u >> i & 1)
        result = scalar_relation(keys, tags, scalar, forced=pins, graphic=graphic)
        if result is not None:
            v, sites = result
            element = wedge(u, v, n)
            if not ((form & element).bit_count() & 1):
                raise AssertionError("wedge does not violate the queried equation")
            return element, u, v, sites
    return None


def paired_space(keys, tags, *, graphic=is_graphic):
    """Return actual (wedge, first mask, second mask, common sites) basis records."""
    rows = first_space(keys, tags, graphic=graphic)
    records = []
    dimension = len(keys) * (len(keys) - 1) // 2
    while True:
        for form in annihilator((r[0] for r in records), dimension):
            record = separate(keys, tags, rows, form, graphic=graphic)
            if record is not None:
                records.append(record)
                break
        else:
            return tuple(records)
