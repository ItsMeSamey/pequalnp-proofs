"""Exact Bareiss determinants and all local coefficients for two prime planes."""
from itertools import combinations


def bareiss(mat):
    a = [row.copy() for row in mat]
    prev, sign = 1, 1
    for i in range(len(a) - 1):
        pivot = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot is None:
            return 0
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            sign = -sign
        for j in range(i + 1, len(a)):
            for k in range(i + 1, len(a)):
                raw = a[j][k] * a[i][i] - a[j][i] * a[i][k]
                a[j][k], rem = divmod(raw, prev)
                assert rem == 0
        prev = a[i][i]
    return sign * a[-1][-1]


def check(q):
    pts = [(a, b, 1) for a in range(q) for b in range(q)]
    pts += [(a, 1, 0) for a in range(q)] + [(1, 0, 0)]
    n = len(pts)
    pairs = list(combinations(range(n), 2))
    inc = [[sum(x * y for x, y in zip(p, l)) % q == 0 for l in pts] for p in pts]
    matrix = []
    for p, r in pairs:
        row = []
        for l, j in pairs:
            edge_masks = [pattern for point, line, pattern in
                          ((p, l, 5), (r, l, 6), (p, j, 9), (r, j, 10))
                          if inc[point][line]]
            matched = int(sorted(edge_masks) in ([5, 10], [6, 9]))
            coefficient = sum((-1) ** mask.bit_count() for mask in range(16)
                              if any((mask & e) == e for e in edge_masks))
            assert coefficient == -matched
            row.append(matched)
        matrix.append(row)
    exp = len(pairs) - n * (q - 1)
    assert abs(bareiss(matrix)) == q ** exp
    print(f"q={q}: all {len(pairs) ** 2} coefficients verified; |det| = {q}^{exp}")


if __name__ == "__main__":
    for order in (2, 3):
        check(order)
