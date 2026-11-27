"""Run the two local hand controls with exact fractions."""
from fractions import Fraction
from itertools import product
from math import comb, factorial


WORDS = tuple(product((0, 1), repeat=2))


def port_means(word, h):
    mean = Fraction(sum(word), 2)
    return tuple(mean + h * (bit - mean) for bit in word)


def positive_units(word, h):
    q, r = port_means(word, h)
    return q * r


def copy_block(h):
    total = 0
    for left, right in product(WORDS, repeat=2):
        weight = positive_units(left, h) * positive_units(right, h)
        for q, r in zip(port_means(left, h), port_means(right, h)):
            weight *= q * r + (1 - q) * (1 - r)
        total += weight
    return total


def main():
    modulus = 128
    h = Fraction(1, 129)
    scalar = sum(positive_units(word, h) for word in WORDS)
    cleared = 16 * 129**4 * scalar
    assert cleared.denominator == 1 and cleared % modulus == 16
    # The eighth forward difference at step 1/8 isolates the top coefficient.
    difference = sum((-1)**j * comb(8, j) * copy_block(Fraction(j, 8))
                     for j in range(9))
    top = difference * 8**8 / factorial(8)
    assert top == Fraction(1, 16)
    assert copy_block(1) - top == Fraction(15, 16)


if __name__ == "__main__":
    main()
