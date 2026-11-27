"""Witnessed Boolean moment basis for binary single-row activation equations."""
from itertools import combinations


def bits(x):
    while x:
        bit = x & -x
        yield bit.bit_length() - 1
        x ^= bit


def insert(pivots, row):
    while row:
        j = row.bit_length() - 1
        if j not in pivots:
            pivots[j] = row
            return True
        row ^= pivots[j]
    return False


def rank(rows):
    pivots = {}
    for row in rows:
        insert(pivots, row)
    return len(pivots)


def blocks(rows):
    reach = [row | (1 << i) for i, row in enumerate(rows)]
    for i in range(len(rows)):
        for j in range(len(rows)):
            if reach[j] & (1 << i):
                reach[j] |= reach[i]
    groups = {}
    for i, closure in enumerate(reach):
        groups[closure] = groups.get(closure, 0) | (1 << i)
    return [groups[c] for c in sorted(groups, key=int.bit_count)]


def correction(rows, support):
    toggles = prefix = 0
    for i in bits(support):
        prefix |= 1 << i
        matrix = [(rows[j] ^ (toggles & (1 << j))) & prefix for j in bits(prefix)]
        if rank(matrix) < len(matrix):
            toggles |= 1 << i
    return toggles


def section(rows, support, rhs, toggles, downstream):
    equations = {}
    for i in bits(support):
        a = (rows[i] ^ (toggles & (1 << i))) & support
        b = ((rows[i] & downstream).bit_count() ^ ((rhs ^ toggles) >> i)) & 1
        while a:
            pivot = a.bit_length() - 1
            if pivot not in equations:
                equations[pivot] = a, b
                break
            other, value = equations[pivot]
            a ^= other
            b ^= value
        else:
            raise ArithmeticError('singular section')
    word = 0
    for i in sorted(equations):
        a, b = equations[i]
        if b ^ ((a & word).bit_count() & 1):
            word |= 1 << i
    return downstream | word


def masks(indices, limit):
    indices = tuple(indices)
    for size in range(min(limit, len(indices)) + 1):
        for subset in combinations(indices, size):
            yield sum(1 << i for i in subset)


def features(x, monomials):
    return sum(1 << j for j, m in enumerate(monomials) if x & m == m)


def basis(rows, rhs, degree):
    rows = tuple(rows)
    n = len(rows)
    if degree < 0 or rhs < 0 or rhs >> n or any(r < 0 or r >> n for r in rows):
        raise ValueError('invalid binary activation input')
    samples = [0]
    processed = 0
    for block in blocks(rows):
        processed |= block
        monomials = list(masks(bits(processed), degree))
        # Kogan's rank-2 approximation: complement a nonsingular diagonal.
        gauges = correction(rows, block) ^ block
        local_rank = rank([(rows[i] ^ (gauges & (1 << i))) & block for i in bits(block)])
        kept = []
        pivots = {}
        for support in masks(bits(block), local_rank + degree):
            toggle = correction(rows, support)
            for old in samples:
                x = section(rows, support, rhs, toggle, old)
                if insert(pivots, features(x, monomials)):
                    kept.append(x)
        samples = kept
    return samples
