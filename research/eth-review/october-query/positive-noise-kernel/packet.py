"""Exact value for a primary packet of distinct signed unit rows."""
from fractions import Fraction
from math import comb


def packet(positive, negative, t):
    size = positive + negative
    t = Fraction(t)
    total = Fraction(0)
    for a in range(positive + 1):
        for b in range(negative + 1):
            p = t * Fraction(a + b, size)
            # a and b are the one bits in the positive and negative rows.
            weight = (1 - t + p)**a * p**(positive - a)
            weight *= (t - p)**b * (1 - p)**(negative - b)
            total += comb(positive, a) * comb(negative, b) * weight
    return total


if __name__ == "__main__":
    from itertools import product
    for size in range(1, 7):
        for pos in range(size + 1):
            for t in map(Fraction, ["0", "1/3", "1"]):
                check = 0
                for word in product(range(2), repeat=size):
                    value = 1
                    for i, x in enumerate(word):
                        q = (1-t)*x + t*Fraction(sum(word), size)
                        value *= q if i < pos else 1-q
                    check += value
                assert packet(pos, size-pos, t) == check
    print("81 exact exhaustive comparisons passed")
