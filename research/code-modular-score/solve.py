"""Walsh/Lucas test for one odd p-group score of affine binary forms."""
from math import comb


def add(poly, key, value, prime):
    value = (poly.get(key, 0) + value) % prime
    if value:
        poly[key] = value
    else:
        poly.pop(key, None)


def multiply(left, right, prime):
    result = {}
    for u, a in left.items():
        for v, b in right.items():
            add(result, u ^ v, a * b, prime)
    return result


def indicator(forms, prime, moduli, target):
    """Each form is (mask, offset, tuple of weights), with moduli powers of prime."""
    if prime == 2:
        raise ValueError("Walsh calculation requires odd characteristic")
    inv_two = pow(2, -1, prime)
    result = {0: 1}
    for coord, (q, t) in enumerate(zip(moduli, target, strict=True)):
        shifted = q - 1 - t % q
        entries = [{0: coeff} if (coeff := comb(shifted, j) % prime) else {}
                   for j in range(q)]
        for mask, offset, weights in forms:
            # d=(1−(−1)^offset X^mask)/2.
            lit = {0: inv_two}
            add(lit, mask, (2 * offset - 1) * inv_two, prime)
            weight = weights[coord] % q
            for degree in range(q - 1, 0, -1):
                for j in range(1, min(degree, weight) + 1):
                    coeff = comb(weight, j) % prime
                    if not coeff:
                        continue
                    for key, val in multiply(entries[degree - j], lit, prime).items():
                        add(entries[degree], key, coeff * val, prime)
        result = multiply(result, entries[-1], prime)
    return result


def witness_mod(spectrum, prime):
    current = spectrum
    assignment = 0
    while current and max(current):
        bit = 1 << (max(current).bit_length() - 1)
        for value in (0, 1):
            restricted = {}
            for key, a in current.items():
                sign = -1 if value and key & bit else 1
                add(restricted, key & ~bit, sign*a, prime)
            if restricted:
                current = restricted
                if value:
                    assignment |= bit
                break
        else:
            raise AssertionError("both restrictions vanished in odd characteristic")
    return assignment if current else None
