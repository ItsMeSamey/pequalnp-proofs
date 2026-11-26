"""Exhaustively compare rank-two witnesses and four-colorings on small graphs."""
from itertools import combinations, product


def singles_pairs(units):
    return list(units) + [a ^ b for a, b in combinations(units, 2)]


def points(n):
    d = 2 * n + 1
    units = [1 << i for i in range(d)]
    pure = singles_pairs(units)
    fixed = [(v, 0) for v in pure] + [(0, v) for v in pure]
    for w in singles_pairs(units[1:]):
        fixed.extend([(w, 1 ^ w), (1 ^ w, w)])
    edges = list(combinations(range(n), 2))
    extra = [(1 ^ units[1 + 2*i] ^ units[1 + 2*j],
              1 ^ units[2 + 2*i] ^ units[2 + 2*j]) for i, j in edges]
    return d, fixed, edges, extra


def evaluations(form, columns):
    return sum(((form & col).bit_count() % 2) << i
               for i, col in enumerate(columns))


def verify(n):
    d, fixed, edges, extra = points(n)
    columns = fixed + extra
    left, right = zip(*columns)
    left_masks = [evaluations(f, left) for f in range(1, 1 << d)]
    right_masks = [evaluations(f, right) for f in range(1, 1 << d)]
    forbidden = (1 << len(fixed)) - 1
    histogram = [0] * (1 << len(edges))
    for a, lmask in enumerate(left_masks, 1):
        for b, rmask in enumerate(right_masks, 1):
            overlap = lmask & rmask
            if overlap & forbidden == 0:
                assert a == b and a & 1
                histogram[overlap >> len(fixed)] += 1
    expected = [0] * len(histogram)
    for coloring in product(range(4), repeat=n):
        bad = sum((coloring[u] == coloring[v]) << k
                  for k, (u, v) in enumerate(edges))
        expected[bad] += 1
    assert histogram == expected
    if n <= 2:
        raw = [l | (r << d) for l, r in columns]
        masks = [evaluations(f, raw) for f in range(1, 1 << (2*d))]
        raw_histogram = [0] * len(histogram)
        for a, b in combinations(masks, 2):
            overlap = a & b
            if overlap & forbidden == 0:
                raw_histogram[overlap >> len(fixed)] += 1
        assert raw_histogram == histogram
    print(f'n={n}: verified all {len(histogram)} graphs')


if __name__ == '__main__':
    for n in range(6):
        verify(n)
