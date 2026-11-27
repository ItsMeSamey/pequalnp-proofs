"""Exact counts and original flag witnesses by polynomial-space Fourier inversion."""

from biclique_period import _basis
from syndrome_dp import _compress


def _factor(indices, columns, pins):
    """Character sum of this shore, with the other shore set to zero."""
    shift = 0
    unknown = []
    for i in indices:
        if pins[i] == 1:
            shift ^= columns[i]
        elif pins[i] < 0:
            unknown.append(columns[i])
    return shift, 1 << len(unknown), tuple(_basis(unknown).values())


def _evaluate(factor, character):
    shift, size, basis = factor
    if any((character & row).bit_count() % 2 for row in basis):
        return 0
    return -size if (character & shift).bit_count() % 2 else size


def _count(columns, target, rank, groups, isolated, pins):
    free = _factor(isolated, columns, pins)
    factors = []
    for left, right in groups:
        left_one = any(pins[i] == 1 for i in left)
        right_one = any(pins[i] == 1 for i in right)
        if left_one and right_one:
            return 0
        shores = []
        if not right_one:
            shores.append(_factor(left, columns, pins))
        if not left_one:
            shores.append(_factor(right, columns, pins))
        overlap = int(not (left_one or right_one))
        factors.append((shores, overlap))
    numerator = 0
    for character in range(1 << rank):
        value = _evaluate(free, character)
        for shores, overlap in factors:
            if not value:
                break
            value *= sum(_evaluate(s, character) for s in shores) - overlap
        if (character & target).bit_count() % 2:
            numerator -= value
        else:
            numerator += value
    return numerator >> rank


def fourier_count_witness(columns, target, components):
    """Return (exact count, original flag bits or None) for a binary syndrome.

    Each component is a disjoint pair of flag-ID shores: assignments may
    select flags from either shore. Unlisted flags are independent. Equal and
    zero syndrome columns still represent distinct physical choices.

    Rank compression is injective on the original column span. At rank r,
    each count streams 2**r characters; witness recovery uses at most n more
    counts. Space is polynomial in the input size. For n physical flags the
    signed inversion numerator has magnitude at most 2**(n+r).
    """
    columns = tuple(columns)
    if not isinstance(target, int) or target < 0 or any(
        not isinstance(x, int) or x < 0 for x in columns
    ):
        raise ValueError("invalid syndrome mask")
    used = bytearray(len(columns))
    groups = []
    for left, right in components:
        pair = tuple(left), tuple(right)
        for shore in pair:
            for i in shore:
                if not isinstance(i, int) or not 0 <= i < len(columns) or used[i]:
                    raise ValueError("invalid or repeated flag index")
                used[i] = 1
        groups.append(pair)
    isolated = tuple(i for i in range(len(columns)) if not used[i])
    cols, t, rank = _compress(columns, target)
    if t is None:
        return 0, None
    pins = [-1] * len(columns)
    total = _count(cols, t, rank, groups, isolated, pins)
    if not total:
        return 0, None
    for i in range(len(pins)):
        pins[i] = 0
        if not _count(cols, t, rank, groups, isolated, pins):
            pins[i] = 1
    return total, pins
