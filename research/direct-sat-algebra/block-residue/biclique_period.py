"""Binary syndrome witnesses for disjoint complete-bipartite conflict components."""

from itertools import product


def _reduce(x, basis):
    """Linear projection modulo an echelon basis, retaining nonpivot bits."""
    for pivot in sorted(basis, reverse=True):
        if (x >> pivot) & 1:
            x ^= basis[pivot]
    return x


def _insert(basis, x):
    x = _reduce(x, basis)
    if x:
        basis[x.bit_length() - 1] = x


def _basis(vectors):
    basis = {}
    for vector in vectors:
        _insert(basis, vector)
    return basis


def _intersection(left, right):
    """Kernel of the projection from the left span modulo the right span."""
    table = {}
    common = []
    for original in left.values():
        image = _reduce(original, right)
        lift = original
        while image:
            pivot = image.bit_length() - 1
            if pivot not in table:
                table[pivot] = image, lift
                break
            row, source = table[pivot]
            image ^= row
            lift ^= source
        else:
            common.append(lift)
    return common


def _solve(columns, ids, target):
    """Solve on the original columns, carrying a flag-index mask as provenance."""
    table = {}
    for i in ids:
        image = columns[i]
        flags = 1 << i
        while image:
            pivot = image.bit_length() - 1
            if pivot not in table:
                table[pivot] = image, flags
                break
            row, source = table[pivot]
            image ^= row
            flags ^= source
    flags = 0
    while target:
        pivot = target.bit_length() - 1
        if pivot not in table:
            return None
        row, source = table[pivot]
        target ^= row
        flags ^= source
    return [(flags >> i) & 1 for i in range(len(columns))]


def biclique_period_witness(columns, target, components):
    """Return original flag bits with the requested XOR, or None.

    Each component supplies (left_ids, right_ids) of a complete bipartite
    conflict graph. Its selected flags must lie in a single shore. Components
    and their two shores must be mutually disjoint. Unlisted flags are free.
    Columns and the target are nonnegative integer masks in a common GF(2)
    coordinate system. Empty shores and repeated column values are supported.
    """
    columns = tuple(columns)
    if not isinstance(target, int) or target < 0 or any(
        not isinstance(x, int) or x < 0 for x in columns
    ):
        raise ValueError("expected nonnegative integer syndrome masks")
    used = bytearray(len(columns))
    active = []
    for left, right in components:
        pair = tuple(left), tuple(right)
        for shore in pair:
            for i in shore:
                if not isinstance(i, int) or not 0 <= i < len(columns) or used[i]:
                    raise ValueError("invalid or repeated flag index")
                used[i] = 1
        active.append(pair)
    fixed = [i for i in range(len(columns)) if not used[i]]
    free = _basis(columns[i] for i in fixed)

    while active:
        gains = []
        remaining = []
        for left, right in active:
            u = _basis(_reduce(columns[i], free) for i in left)
            v = _basis(_reduce(columns[i], free) for i in right)
            common = _intersection(u, v)
            if len(common) == len(u):
                # In the quotient the right shore contains the left.
                fixed.extend(right)
                gains.extend(v.values())
            elif len(common) == len(v):
                fixed.extend(left)
                gains.extend(u.values())
            else:
                remaining.append((left, right))
                gains.extend(common)
        active = remaining
        if not gains:
            break
        for vector in gains:
            _insert(free, vector)

    # Each free direction is available for every still-permitted orientation
    # (inductively, using fixed shores and the two-shore intersections).
    # Original-coordinate solving therefore recovers all quotient lifts.
    for choices in product((0, 1), repeat=len(active)):
        ids = fixed.copy()
        for pair, side in zip(active, choices):
            ids.extend(pair[side])
        witness = _solve(columns, ids, target)
        if witness is not None:
            return witness
    return None
