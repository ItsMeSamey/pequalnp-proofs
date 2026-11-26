"""Compare exact rational ranks of cycle truth tables with the row-cut formula."""
from fractions import Fraction
from itertools import permutations
from math import comb


def cycle_rows(n, k):
    rows = {}
    for tail in permutations(range(1, n)):
        order = (0,) + tail
        image = [None] * n
        for vertex, successor in zip(order, order[1:] + (0,)):
            image[vertex] = successor
        row = rows.setdefault(tuple(image[:k]), {})
        row[tuple(image[k:])] = Fraction(1)
    return rows.values()


def rational_rank(rows):
    pivots = {}
    for vector in rows:
        row = vector.copy()
        while row:
            key = min(row)
            value = row[key]
            if key not in pivots:
                pivots[key] = {i: a / value for i, a in row.items()}
                break
            for i, a in pivots[key].items():
                remainder = row.get(i, 0) - value * a
                if remainder:
                    row[i] = remainder
                else:
                    row.pop(i, None)
    return len(pivots)


if __name__ == "__main__":
    for n in range(1, 8):
        ranks = []
        for k in range(n + 1):
            rank = rational_rank(cycle_rows(n, k))
            expected = sum(comb(k, m) * comb(n-k, m) * comb(2*m-2, m-1)
                           for m in range(1, min(k, n-k) + 1))
            assert rank == (expected if 0 < k < n else 1), (n, k, rank)
            ranks.append(rank)
        print(n, ranks)
