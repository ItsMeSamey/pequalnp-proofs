"""Exact counts and original-coordinate witnesses for a recognized projective layer."""
from affine_projective_layer import recognize


def _reduce(rows, mask, payload):
    while mask:
        pivot = mask.bit_length() - 1
        if pivot not in rows:
            break
        vector, value = rows[pivot]
        mask ^= vector
        payload ^= value
    return mask, payload


def _insert(rows, mask, value):
    mask, value = _reduce(rows, mask, value)
    if mask:
        rows[mask.bit_length()-1] = (mask, value)
    return bool(mask) or value == 0


def _one_solution(rows):
    result = 0
    for pivot in sorted(rows):
        mask, rhs = rows[pivot]
        if ((mask & result).bit_count() & 1) != rhs:
            result |= 1 << pivot
    return result


def count_layer(n, pairs, complement, flats):
    """Return (count, witness bitmask or None), or None if recognition fails.

    pairs lists pairs of independent original normal masks. complement lists
    further normal masks; together they must be independent and span every
    input normal. Each flat (p,q,a,b) forbids p·x=a AND q·x=b over F_2.
    """
    if not isinstance(n, int) or n < 0:
        raise ValueError("invalid ambient dimension")
    pairs, complement, flats = list(pairs), list(complement), list(flats)
    basis = [v for u, w in pairs for v in (u, w)] + complement
    dimension = len(basis)
    pivots = {}
    for i, vector in enumerate(basis):
        if not isinstance(vector, int) or vector <= 0 or vector.bit_length() > n:
            raise ValueError("invalid basis vector")
        mask, coordinates = _reduce(pivots, vector, 1 << i)
        if not mask:
            raise ValueError("dependent normal basis")
        pivots[mask.bit_length()-1] = mask, coordinates

    blocks = []
    for p, q, a, b in flats:
        if p == q or any(not isinstance(v, int) or v <= 0 or v.bit_length() > n for v in (p,q)):
            raise ValueError("expected two independent normal masks")
        if a not in (0, 1) or b not in (0, 1):
            raise ValueError("expected binary offsets")
        mp, cp = _reduce(pivots, p, 0)
        mq, cq = _reduce(pivots, q, 0)
        if mp or mq:
            raise ValueError("gate normal outside supplied basis span")
        blocks.append([((cp >> (2*i)) & 3) | (((cq >> (2*i)) & 3) << 2)
                       for i in range(len(pairs))])
    labels = recognize(blocks, len(pairs))
    if labels is None:
        return None
    gates, lines = labels
    layer = [((p if label & 1 else 0) ^ (q if label & 2 else 0))
             for (p,q), label in zip(pairs, lines)] + complement
    total = 0
    witness = None
    for assignment in range(1 << (dimension-len(pairs))):
        equations = {}
        for i, normal in enumerate(layer):
            _insert(equations, normal, (assignment >> i) & 1)
        # All gate lines lie in this fiber's equation span. If the chosen
        # normal agrees with its forbidden value, force the other one opposite.
        for (p,q,a,b), gate in zip(flats, gates):
            normal = (p if gate & 1 else 0) ^ (q if gate & 2 else 0)
            residue, value = _reduce(equations, normal, 0)
            assert residue == 0
            forbidden = (a if gate & 1 else 0) ^ (b if gate & 2 else 0)
            if value != forbidden:
                continue
            other, rhs = (q,b) if gate == 1 else (p,a)
            if not _insert(equations, other, rhs ^ 1):
                break
        else:
            total += 1 << (n-len(equations))
            if witness is None:
                witness = _one_solution(equations)
    return total, witness
