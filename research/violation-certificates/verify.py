"""Exhaustive exact checks of the clause-violation Gram certificate."""
from fractions import Fraction
from itertools import combinations, product
from functools import cache


def solve(rows, width):
    basis = {}
    for row in rows:
        row = list(map(Fraction, row))
        for pivot in sorted(basis):
            if row[pivot]:
                ratio = row[pivot]
                row = [a - ratio * b for a, b in zip(row, basis[pivot])]
        pivot = next((i for i in range(width) if row[i]), None)
        if pivot is None:
            if row[-1]:
                return None
        else:
            basis[pivot] = [a / row[pivot] for a in row]
    result = [Fraction(0)] * width
    for pivot in sorted(basis, reverse=True):
        row = basis[pivot]
        result[pivot] = row[-1] - sum(a*b for a, b in zip(row[pivot+1:-1], result[pivot+1:]))
    return result


def check(n, clauses, degree):
    # Each clause lists the partial assignment that falsifies it, via -1 wildcards.
    features = [frozenset(s) for k in range(1, degree+1)
                for s in combinations(range(len(clauses)), k)]
    @cache
    def joint(indices):
        free = 0
        for i in range(n):
            needs = {clauses[j][i] for j in indices} - {-1}
            if len(needs) == 2:
                return 0
            free += not needs
        return 2**free

    def weighted(indices):
        return sum(joint(indices | {i}) for i in range(len(clauses)))

    rhs = [weighted(s) for s in features]
    rows = [[weighted(s | t) for t in features] + [r] for s, r in zip(features, rhs)]
    weights = solve(rows, len(features))
    assert weights is not None
    fits = weighted(frozenset()) == sum(a*b for a, b in zip(weights, rhs))
    models = 0
    table = []
    for bits in product(range(2), repeat=n):
        violations = {j for j, c in enumerate(clauses) if all(
            v == -1 or v == b for v, b in zip(c, bits))}
        if violations:
            table.append([s <= violations for s in features] + [1])
        else:
            models += 1
    assert fits == (solve(table, len(features)) is not None)
    if fits:
        assert models == 2**n - sum(w*joint(s) for w, s in zip(weights, features))
    return fits


if __name__ == '__main__':
    for n, limit in [(0, 1), (1, 3), (2, 9), (3, 3)]:
        clauses = list(product((-1, 0, 1), repeat=n))
        for degree in (1, 2):
            passed = total = 0
            for k in range(limit + 1):
                for formula in combinations(clauses, k):
                    passed += check(n, formula, degree)
                    total += 1
            print(n, degree, passed, total, flush=True)
