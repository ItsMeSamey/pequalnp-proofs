"""Common primal directions certified by squarefree degree-two dual equations."""

from itertools import product

from biclique_period import _basis, _insert, _intersection, _reduce, _solve


def dual_directions(shore_bases):
    """Return independent linear consequences of dual shore-product equations.

    Each input pair contains iterables of quotient vectors, given as integer
    bitmasks in one fixed coordinate system. Results use that coordinate system.
    """
    monomials = {}
    quadratic = {}
    linear = {}
    for left, right in shore_bases:
        right = tuple(right)
        for u in left:
            for v in right:
                # Squares give the linear part. Assign IDs only to off-diagonal
                # monomials present in a product, even for sparse coordinates.
                h = u & v
                q = 0
                a = u
                while a:
                    i = (a & -a).bit_length() - 1
                    a &= a - 1
                    b = v & ~(1 << i)
                    while b:
                        j = (b & -b).bit_length() - 1
                        b &= b - 1
                        pair = (min(i, j), max(i, j))
                        k = monomials.setdefault(pair, len(monomials))
                        q ^= 1 << k
                while q:
                    p = q.bit_length() - 1
                    if p not in quadratic:
                        quadratic[p] = q, h
                        break
                    row, tail = quadratic[p]
                    q ^= row
                    h ^= tail
                else:
                    _insert(linear, h)
    return tuple(linear.values())


def biclique_dual_witness(columns, target, components):
    """Find original flags for disjoint bicliques, or return None.

    Inputs and output follow biclique_period.biclique_period_witness.
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
        dual_pairs = []
        for left, right in active:
            u = _basis(_reduce(columns[i], free) for i in left)
            v = _basis(_reduce(columns[i], free) for i in right)
            common = _intersection(u, v)
            if len(common) == len(u):
                fixed.extend(right)
                gains.extend(v.values())
            elif len(common) == len(v):
                fixed.extend(left)
                gains.extend(u.values())
            else:
                remaining.append((left, right))
                dual_pairs.append((tuple(u.values()), tuple(v.values())))
                gains.extend(common)
        active = remaining
        if not gains:
            gains.extend(dual_directions(dual_pairs))
        if not gains:
            break
        for h in gains:
            _insert(free, h)
    for choices in product((0, 1), repeat=len(active)):
        ids = fixed.copy()
        for pair, side in zip(active, choices):
            ids.extend(pair[side])
        witness = _solve(columns, ids, target)
        if witness is not None:
            return witness
    return None
