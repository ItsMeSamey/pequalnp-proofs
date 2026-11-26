"""Deterministic target search for a map given with a valid coordinate-degree bound."""
from functools import lru_cache


def remainder(a, b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def multiply(a, b, modulus):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a = remainder(a << 1, modulus)
        b >>= 1
    return result


@lru_cache(maxsize=None)
def field_modulus(ell):
    """Trial division suffices here: at most O(2^(3ell/2) poly(ell)) work."""
    if ell < 1:
        raise ValueError("field degree must be positive")
    for candidate in range((1 << ell) + 1, 2 << ell, 2):
        if all(remainder(candidate, divisor)
               for divisor in range(2, 1 << (ell // 2 + 1))):
            return candidate
    raise AssertionError("missing irreducible polynomial")


def block(n, a, b, modulus):
    out = 0
    for j in range(n):
        out |= (b & 1) << j
        b = multiply(a, b, modulus)
    return out


def sample(n, d, ell, seed):
    """Map a 2*d*ell-bit seed to an n-bit integer."""
    if min(n, d, seed) < 0 or ell < 1 or seed.bit_length() > 2*d*ell:
        raise ValueError("invalid generator arguments")
    mask = (1 << ell) - 1
    modulus = field_modulus(ell)
    out = 0
    for _ in range(d):
        a = seed & mask
        b = (seed >> ell) & mask
        out ^= block(n, a, b, modulus)
        seed >>= 2 * ell
    return out


def field_degree(n, d, t):
    if min(n, d, t) < 1:
        raise ValueError("positive parameters required")
    return (n - 1).bit_length() + ((d*t + 5) << (d - 1))


def find_target(n, d, t, target, evaluate):
    """evaluate(x) returns (t-bit value, witness). Return (x,witness) or None."""
    if min(n, d, t, target) < 0 or target.bit_length() > t:
        raise ValueError("invalid map parameters")
    d = min(d, n)
    if not (d and t):
        points = (0,)
    else:
        ell = field_degree(n, d, t)
        width = 2 * d * ell
        points = (range(1 << n) if n <= width else
                  (sample(n, d, ell, seed) for seed in range(1 << width)))
    for x in points:
        value, witness = evaluate(x)
        if value == target:
            return x, witness
    return None
