"""Elementary arbitrary-rank simultaneous coordinate bases over GF(2)."""
from ring_image_affine_hull_sparse import Span, _combine


def span(vectors):
    result = Span()
    for v in vectors:
        result.append(v)
    return result


def _block_lifts(word_rows, containing, exact):
    # Eliminate the projection of W outside U_T. Zero remainders give
    # a spanning set of W intersect U_T, in old basis coordinates.
    outside = {}
    projected = Span()
    lifts = []
    for word in word_rows:
        residual = word & ~containing
        while residual:
            p = residual.bit_length() - 1
            if p not in outside:
                outside[p] = residual, word
                break
            left, right = outside[p]
            residual ^= left
            word ^= right
        else:
            if projected.append(word & exact):
                lifts.append(word)
    split = len(lifts)
    bits = exact
    while bits:
        bit = bits & -bits
        if projected.append(bit):
            lifts.append(bit)
        bits ^= bit
    return lifts, split


def common_basis(n, spaces):
    """Return ambient axes and per-axis incidence masks, or None."""
    if type(n) is not int or n < 0:
        raise ValueError("invalid ambient dimension")
    axes = [1 << i for i in range(n)]
    signatures = [0] * n
    original = []
    for i, vectors in enumerate(spaces):
        vectors = tuple(vectors)
        if any(type(v) is not int or v < 0 or v.bit_length() > n for v in vectors):
            raise ValueError("invalid subspace vector")
        space = span(vectors)
        original.append(space)
        old = span(axes)
        words = [old.decompose(v)[1] for v in space.axes]
        blocks = {}
        for j,t in enumerate(signatures):
            blocks[t] = blocks.get(t, 0) | (1 << j)
        replacements = []
        new_signatures = []
        total = 0
        for t, exact in blocks.items():
            containing = 0
            for s, block in blocks.items():
                if s & t == t:
                    containing |= block
            lifts, split = _block_lifts(words, containing, exact)
            total += split
            for j, word in enumerate(lifts):
                replacements.append(_combine(axes, word))
                new_signatures.append(t | (1 << i) if j < split else t)
        if total != len(space.axes):
            return None
        axes, signatures = replacements, new_signatures
    if len(span(axes).axes) != n:
        raise AssertionError("nonbasis output")
    for i, space in enumerate(original):
        included = [a for a,t in zip(axes, signatures) if t >> i & 1]
        if len(included) != len(space.axes) or any(space.decompose(a)[0] for a in included):
            raise AssertionError("invalid coordinate subspace certificate")
    return axes, signatures
