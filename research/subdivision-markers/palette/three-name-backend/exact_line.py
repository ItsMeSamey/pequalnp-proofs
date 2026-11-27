"""Exact prescribed line for indexed GF(2) columns encoded by nonnegative integers."""
from separations import find_separation
from graphic import is_graphic


def pivots(columns):
    table = {}
    for col in columns:
        if col < 0:
            raise ValueError("negative binary column")
        while col:
            bit = col.bit_length() - 1
            if bit not in table:
                table[bit] = col
                break
            col ^= table[bit]
    return table


def quotient(col, table):
    for bit in sorted(table, reverse=True):
        if col & (1 << bit):
            col ^= table[bit]
    return col


def interface(left, right):
    """Lift a basis of the kernel of span(right) -> ambient/span(left)."""
    table = pivots(left)
    lifted = {}
    result = []
    for original in pivots(right).values():
        rem = quotient(original, table)
        while rem:
            bit = rem.bit_length() - 1
            if bit not in lifted:
                lifted[bit] = rem, original
                break
            step, preimage = lifted[bit]
            rem ^= step
            original ^= preimage
        if not rem:
            result.append(original)
    return result


def line_decision(ordinary, target, a, b, *, graphic=is_graphic):
    """target,a,b is a basis of the named space."""
    ordinary = list(ordinary)
    if len(pivots((target, a, b))) != 3:
        raise ValueError("dependent named basis")
    if target in ordinary:
        return True
    if quotient(target, pivots(ordinary)):
        return False
    c = target ^ a ^ b
    columns = [a, b, c, a ^ b, b ^ c, c ^ a] + ordinary
    roots = tuple(range(6))
    while True:
        split = find_separation(columns, roots)
        if split is None:
            return not graphic(columns)
        keep, drop = split
        assert set(roots) <= set(keep)
        left = [columns[i] for i in sorted(keep)]
        boundary = interface(left, (columns[i] for i in sorted(drop)))
        assert len(boundary) <= 2 and len(pivots(left)) < len(pivots(columns))
        columns = left + boundary
        if len(boundary) == 2:
            columns.append(boundary[0] ^ boundary[1])


def exact_line(ordinary, target, a, b, *, forced=(), graphic=is_graphic):
    """Return original positions including all pins, or None."""
    ordinary = tuple(ordinary)
    if any(col < 0 for col in ordinary):
        raise ValueError("negative ordinary column")
    pins = frozenset(forced)
    if any(i < 0 or i >= len(ordinary) for i in pins):
        raise ValueError("forced position out of range")
    if len(pivots((target, a, b))) != 3:
        raise ValueError("dependent named basis")
    table = pivots(ordinary[i] for i in pins)
    qtarget, qa, qb = (quotient(x, table) for x in (target, a, b))
    if len(pivots((qtarget, qa, qb))) < 3:
        if qtarget == 0 and len(pivots((qa, qb))) == 2:
            return tuple(sorted(pins))
        return None
    ids = [i for i in range(len(ordinary)) if i not in pins]
    reduced = {i: quotient(ordinary[i], table) for i in ids}

    def accepts(indices):
        return line_decision((reduced[i] for i in indices), qtarget, qa, qb, graphic=graphic)

    if not accepts(ids):
        return None
    for i in tuple(ids):
        trial = [j for j in ids if i != j]
        if accepts(trial):
            ids = trial
    witness = tuple(sorted([*pins, *ids]))
    check = pivots(ordinary[i] for i in witness)
    if quotient(target, check) or len(pivots(quotient(x, check) for x in (a, b))) != 2:
        raise AssertionError("invalid lifted exact-line witness")
    return witness
