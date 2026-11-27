"""Capped sparse violation histogram. CLI reads JSON with n, clauses, cap."""
import json
import sys
from fractions import Fraction


def evaluation_basis(words, width):
    """Independent indicator monomials in nondecreasing degree."""
    chosen = []
    echelon = []
    seen = set()
    frontier = [0]
    while frontier:
        children = []
        for mask in frontier:
            if mask in seen:
                continue
            seen.add(mask)
            row = [Fraction((word & mask) == mask) for word in words]
            for pivot, vector in echelon:
                if row[pivot]:
                    factor = row[pivot]
                    row = [a - factor * b for a, b in zip(row, vector)]
            pivot = next((j for j, a in enumerate(row) if a), None)
            if pivot is None:
                continue
            echelon.append((pivot, [a / row[pivot] for a in row]))
            chosen.append(mask)
            if len(chosen) == len(words):
                return chosen
            for j in range(width):
                if not (mask >> j) & 1:
                    children.append(mask | (1 << j))
        frontier = children
    raise ArithmeticError("prefix evaluations did not span")


def split_masses(words, masks, moments):
    rows = [[Fraction((word & mask) == mask) for word in words] + [Fraction(value)]
            for mask, value in zip(masks, moments)]
    for j in range(len(words)):
        pivot = next(i for i in range(j, len(rows)) if rows[i][j])
        rows[j], rows[pivot] = rows[pivot], rows[j]
        rows[j] = [v / rows[j][j] for v in rows[j]]
        for i, row in enumerate(rows):
            if i != j and row[j]:
                factor = row[j]
                rows[i] = [a - factor * b for a, b in zip(row, rows[j])]
    result = [row[-1] for row in rows]
    if any(x.denominator != 1 for x in result):
        raise ArithmeticError("nonintegral child mass")
    return [int(x) for x in result]


def count_cnf(n, clauses, cap):
    if type(n) is not int or n < 0 or type(cap) is not int or cap < 0:
        raise ValueError("n and cap must be nonnegative integers")
    pins = []
    for clause in clauses:
        zeros = ones = 0
        for literal in clause:
            if type(literal) is not int or not 1 <= abs(literal) <= n:
                raise ValueError("literal outside declared variable range")
            bit = 1 << (abs(literal) - 1)
            if literal > 0:
                zeros |= bit
            else:
                ones |= bit
        pins.append((zeros, ones))

    def moment(mask):
        zeros = ones = 0
        while mask:
            bit = mask & -mask
            a, b = pins[bit.bit_length() - 1]
            zeros |= a
            ones |= b
            if zeros & ones:
                return 0
            mask ^= bit
        return 1 << (n - (zeros | ones).bit_count())

    histogram = {0: 1 << n}
    for j in range(len(pins)):
        words = list(histogram)
        masks = evaluation_basis(words, j)
        bit = 1 << j
        children = split_masses(words, masks, [moment(mask | bit) for mask in masks])
        updated = {}
        for word, one in zip(words, children):
            zero = histogram[word] - one
            if min(zero, one) < 0:
                raise ArithmeticError("negative child mass")
            if zero:
                updated[word] = zero
            if one:
                updated[word | bit] = one
        histogram = updated
        if len(histogram) - int(0 in histogram) > cap:
            return {"status": "overflow"}
    return {"status": "exact", "count": histogram.get(0, 0), "histogram": histogram}


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    print(json.dumps(count_cnf(**json.load(sys.stdin))))
