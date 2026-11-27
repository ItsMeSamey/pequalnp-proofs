"""Compile NAND circuits through a four-site decoder for each original bit.

The first 3n sites are consecutive triples (a_i, c_i, e_i), followed by
the n tail sites t_i. Packed assignments store site zero most significantly.
"""
from primitive_forecast_extractor import _natural, _source


def _word(width, value):
    if type(value) is not int or value < 0 or value.bit_length() > width:
        raise ValueError("word outside its public width")


def _offset(n, free):
    shift = 0
    for i in range(n):
        triple = (free >> (3 * (n - i - 1))) & 7
        a = triple >> 2
        c = (triple >> 1) & 1
        e = triple & 1
        shift = (shift << 1) | (a ^ (c & e))
    return shift


def decode(n, x):
    """Recover the n source bits from one 4n-bit assignment."""
    _natural(n, "n")
    _word(4 * n, x)
    return (x & ((1 << n) - 1)) ^ _offset(n, x >> n)


def lift(n, y, free):
    """Lift y at the specified 3n-bit free prefix."""
    _natural(n, "n")
    _word(n, y)
    _word(3 * n, free)
    return (free << n) | (y ^ _offset(n, free))


def compile_source(n, F):
    """Return an ordered 4n-input NAND circuit using exactly 10n+s gates."""
    _natural(n, "n")
    source, output = _source(n, F)
    gates = []

    def nand(left, right):
        gates.append((left, right))
        return 4 * n + len(gates) - 1

    def exclusive_or(left, right):
        shared = nand(left, right)
        return nand(nand(left, shared), nand(right, shared))

    image = {-1: -1, -2: -2}
    for i in range(n):
        a, c, e, tail = 3 * i, 3 * i + 1, 3 * i + 2, 3 * n + i
        negated_product = nand(c, e)
        product = nand(negated_product, negated_product)
        image[i] = exclusive_or(exclusive_or(a, tail), product)
    for wire, (left, right) in enumerate(source, n):
        image[wire] = nand(image[left], image[right])
    return tuple(gates), image[output]
