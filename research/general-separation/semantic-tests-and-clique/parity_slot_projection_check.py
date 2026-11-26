"""Exhaustive small check of the common-slot projection and heavy-variable split."""
from itertools import product
from fractions import Fraction
from math import prod

def check(n, r, counts, cutoff):
    choices = list(product(range(r), repeat=n))
    means = [Fraction(sum(c > cutoff for c in row), r) for row in counts]
    histogram = [0] * (n + 1)
    for slots in choices:
        hits = [row[i] for row, i in zip(counts, slots)]
        h = sum(c > cutoff for c in hits)
        histogram[h] += 1
        assert sum(c for c in hits if c <= cutoff) <= (n - h) * cutoff
        for bits in product(range(2), repeat=n):
            blocks = [[bits[j] if i == slots[j] else 0 for i in range(r)] for j in range(n)]
            assert [sum(b) % 2 for b in blocks] == list(bits)
    for h, count in enumerate(histogram):
        mass = sum(prod(p if bit else 1-p for bit, p in zip(flags, means))
                   for flags in product(range(2), repeat=n) if sum(flags) == h)
        assert mass == Fraction(count, len(choices))
    return histogram

if __name__ == '__main__':
    for raw in product(range(3), repeat=6):
        check(3, 2, [raw[0:2], raw[2:4], raw[4:6]], 1)
    print('729 occurrence arrays, 5832 slot projections, 46656 bit assignments passed')
