"""Exact GF(2) boundary-minor and polynomial-feature enumeration; standard library."""
from itertools import combinations
from collections import Counter


def reduce_vector(vector, basis):
    while vector and vector.bit_length() - 1 in basis:
        vector ^= basis[vector.bit_length() - 1]
    return vector


def echelon(rows):
    basis = {}
    for row in rows:
        residual = reduce_vector(row, basis)
        if residual:
            basis[residual.bit_length() - 1] = residual
    return basis


def minor(matrix, dropped_rows=(), dropped_cols=()):
    keep = sum(1 << i for i in range(len(matrix)) if i not in dropped_cols)
    rows = [row & keep for i, row in enumerate(matrix) if i not in dropped_rows]
    return int(len(echelon(rows)) == len(rows))


def border_matrices():
    # Pivot any nonsingular free block away. The remaining free/free block is
    # zero, with rows incident to the three terminals. Invertible row operations
    # on this free block and transposed column operations preserve every channel.
    for h in range(4):
        spans = set()
        for basis in combinations(range(1, 8), h):
            span = {0}
            for v in basis:
                span |= {u ^ v for u in span}
            if len(span) != 1 << h or frozenset(span) in spans:
                continue
            spans.add(frozenset(span))
            for upper in range(64):
                rows = [0, 0, 0, *basis]
                for bit, (i, j) in enumerate((i, j) for i in range(3) for j in range(i, 3)):
                    if upper >> bit & 1:
                        rows[i] |= 1 << j
                        rows[j] |= 1 << i
                for i, row in enumerate(basis, 3):
                    for j in range(3):
                        rows[j] |= ((row >> j) & 1) << i
                yield rows
    # Any dependent free rows yield identically zero for all bordered minors.
    yield [0] * 4


def channel_keys():
    for size in range(4):
        subsets = list(combinations(range(3), size))
        for i, rows in enumerate(subsets):
            for cols in subsets[i:]:
                yield rows, cols


def enumerate_states():
    keys = list(channel_keys())
    assert len(keys) == 14
    states = {}
    signatures = set()
    for matrix in border_matrices():
        bits = [minor([row ^ (d & (1 << i)) for i, row in enumerate(matrix)])
                for d in range(8)]
        signature = sum(bit << i for i, bit in enumerate(bits))
        signatures.add(signature)
        isolates = [d for d in range(8) if bits[d] and all(
            not bits[d ^ step] for step in (1, 2, 4))]
        values = {key: minor(matrix, *key) for key in keys}
        state = sum(values[key] << i for i, key in enumerate(keys))
        fixed, fiber = 0 in isolates, bool(isolates)
        a = values[(), ()]
        b = values[(0, 1, 2), (0, 1, 2)]
        jacobi = a * b
        for i in range(3):
            j, k = sorted({0, 1, 2} - {i})
            jacobi ^= a * values[(i,), (i,)] * values[(j,), (k,)]
        assert jacobi == fixed
        assert states.setdefault(state, (fixed, fiber)) == (fixed, fiber)
    assert len(states) == len(signatures) == 136
    return states


def span_test(states, mode, degree):
    monomials = [sum(1 << i for i in c) for size in range(degree + 1)
                 for c in combinations(range(14), size)]
    def features(state):
        return sum(1 << j for j, support in enumerate(monomials)
                   if state & support == support)
    basis = echelon(features(s) for s in states if not states[s][mode])
    blocked = sum(not reduce_vector(features(s), basis) for s in states if states[s][mode])
    return len(basis), blocked


def main():
    states = enumerate_states()
    print("fixed/fiber distribution", sorted(Counter(states.values()).items()))
    for mode, name in enumerate(("fixed", "fiber")):
        results = [span_test(states, mode, degree) for degree in (1, 2, 3)]
        expected = ([(15, 8), (85, 8), (128, 0)],
                    [(15, 30), (85, 30), (106, 0)])
        assert results == expected[mode]
        print(name, results)


if __name__ == "__main__":
    main()
