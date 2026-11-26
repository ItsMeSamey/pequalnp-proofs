"""A guard (head, literals) permits head=1 only if an affine literal is true.
Literal (mask,constant) has truth parity(mask & x) XOR constant.
Marker (mask,rhs) requires parity(mask & x) = rhs.
"""
from itertools import combinations


def count_flat(n, equations):
    rows = {}
    for mask, rhs in equations:
        while mask:
            p = mask.bit_length() - 1
            if p not in rows:
                rows[p] = mask, rhs
                break
            v, c = rows[p]
            mask ^= v
            rhs ^= c
        if not mask and rhs:
            return 0
    return 1 << (n - len(rows))


def difference_count(n, slice_rows, forbidden):
    result = 0
    for t in range(len(forbidden) + 1):
        sign = (-1) ** t
        for subset in combinations(forbidden, t):
            equations = slice_rows + tuple(row for flat in subset for row in flat)
            result += sign * count_flat(n, equations)
    return result


def solve(n, guards, markers):
    """Return (witness or None, number of exception flats used)."""
    markers = tuple(markers)
    if not count_flat(n, markers):
        return None, 0
    active = []
    for head, literals in guards:
        flat = ((1 << head, 1), *literals)
        count = count_flat(n, markers + flat)
        if count:
            active.append((count, flat))
    active.sort(key=lambda item: -item[0])
    flats = [f for _, f in active]

    for limit in range(len(flats) + 1):
        core, tail = flats[:limit], flats[limit:]
        feasible = difference_count(n, markers, core)
        if not feasible:
            return None, limit

        def lower(equations):
            return difference_count(n, equations, core) - sum(
                difference_count(n, equations + f, core) for f in tail)

        if lower(markers) <= 0:
            continue
        prefix, witness = markers, 0
        for i in range(n):
            zero = prefix + ((1 << i, 0),)
            if lower(zero) > 0:
                prefix = zero
            else:
                prefix += ((1 << i, 1),)
                witness |= 1 << i
        return witness, limit
    raise AssertionError("empty tail gives exact count")
