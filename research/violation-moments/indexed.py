"""Recover joint violation probabilities. Oracle returns -log2(p), or None if p=0."""
from fractions import Fraction
from itertools import combinations


def intersection(indices, query):
    total = 0
    for size in range(1, len(indices) + 1):
        sign = 1 if size % 2 else -1
        for subfamily in combinations(indices, size):
            total += sign * query(subfamily)
    return total


def add_independent(row, echelon):
    v = list(map(Fraction, row))
    for pivot, line in sorted(echelon.items()):
        coeff = v[pivot]
        if coeff:
            v = [a - coeff * b for a, b in zip(v, line)]
    for pivot, coeff in enumerate(v):
        if coeff:
            echelon[pivot] = [a / coeff for a in v]
            return True
    return False


def basis(patterns, coords, degree):
    rows = [((), (1,) * len(patterns))]
    echelon = {}
    add_independent(rows[0][1], echelon)
    for _ in range(degree):
        if len(rows) == len(patterns):
            break
        for support, row in list(rows):
            for j in coords:
                if j in support:
                    continue
                candidate = tuple(a * int(j in p) for a, p in zip(row, patterns))
                if add_independent(candidate, echelon):
                    rows.append((support + (j,), candidate))
                    if len(rows) == len(patterns):
                        return rows
    if len(rows) != len(patterns):
        raise ValueError("width bound inconsistent with prefix support")
    return rows


def solve(rows, rhs):
    mat = [list(map(Fraction, row)) + [Fraction(b)] for row, b in zip(rows, rhs)]
    n = len(mat)
    for j in range(n):
        pivot = next(i for i in range(j, n) if mat[i][j])
        mat[j], mat[pivot] = mat[pivot], mat[j]
        divisor = mat[j][j]
        mat[j] = [x / divisor for x in mat[j]]
        for i in range(n):
            if i != j and mat[i][j]:
                coeff = mat[i][j]
                mat[i] = [a - coeff * b for a, b in zip(mat[i], mat[j])]
    answer = [row[-1] for row in mat]
    if any(v.denominator != 1 for v in answer):
        raise ValueError("inconsistent oracle moments")
    return list(map(int, answer))


def anchor_patterns(anchor, coords, width, query):
    counts = {frozenset(): query((anchor,))}
    seen = []
    for j in coords:
        patterns = list(counts)
        equations = basis(patterns, seen, width.bit_length() - 1)
        rhs = [intersection((anchor, j) + support, query) for support, _ in equations]
        ones = solve([row for _, row in equations], rhs)
        extended = {}
        for pattern, n1 in zip(patterns, ones):
            n0 = counts[pattern] - n1
            if min(n0, n1) < 0:
                raise ValueError("inconsistent pattern counts")
            if n0:
                extended[pattern] = n0
            if n1:
                extended[pattern | {j}] = n1
        counts = extended
        seen.append(j)
    return counts


def joint_exponent(target, width, query):
    """Queries index sets of size at most floor(log2(width)) + 2."""
    if width < 1:
        raise ValueError("use a positive upper bound for clause width")
    ordered = list(dict.fromkeys(target))
    for size in (1, 2):
        if any(query(sub) is None for sub in combinations(ordered, size)):
            return None
    total = 0
    for pos, i in enumerate(ordered):
        if query((i,)) == 0:  # empty scope
            continue
        counts = anchor_patterns(i, ordered[:pos], width, query)
        total += counts.get(frozenset(), 0)
    return total
