"""Recover an integer histogram from its available signed-character sums."""
from collections import Counter
from functools import lru_cache

from sympy import Matrix


def restricted_characters(prefixes, length):
    masks = [0]
    vectors = [[1] * len(prefixes)]
    for bit in range(length):
        old_masks = list(masks)
        for mask in old_masks:
            candidate = mask | (1 << bit)
            signs = [(-1) ** ((prefix & candidate).bit_count()) for prefix in prefixes]
            if Matrix(vectors + [signs]).rank() > len(vectors):
                vectors.append(signs)
                masks.append(candidate)
        if len(vectors) == len(prefixes):
            break
    assert len(vectors) == len(prefixes)
    return masks, Matrix(vectors)


def histogram(length, signed_sum):
    size = signed_sum(0)
    if not size:
        return {}
    counts = {0: size}
    for bit in range(length):
        prefixes = sorted(counts)
        masks, matrix = restricted_characters(prefixes, bit)
        moments = Matrix([signed_sum(mask | (1 << bit)) for mask in masks])
        differences = matrix.inv() * moments
        after = {}
        for prefix, diff in zip(prefixes, differences):
            assert diff.is_Integer
            zero, rem = divmod(counts[prefix] + int(diff), 2)
            assert rem == 0 and 0 <= zero <= counts[prefix]
            if zero:
                after[prefix] = zero
            if counts[prefix] > zero:
                after[prefix | (1 << bit)] = counts[prefix] - zero
        counts = after
    return counts


def check():
    from torus_carry_count import point_count
    from punctured_witness import BinaryField
    from frobenius_drift import power

    field = BinaryField(7)
    terms = [(1, 1), (2, 1), (1, 3), (2, 2), (2, 1)]
    @lru_cache(None)
    def character(mask):
        equation = {(0, 2): 1, (0, 1): 1}
        for j, (coefficient, exponent) in enumerate(terms):
            if mask & (1 << j):
                key = (exponent, 0)
                equation[key] = equation.get(key, 0) ^ coefficient
        return point_count(field, equation) - field.size

    expected = Counter()
    for x in range(field.size):
        word = 0
        for j, (a, exponent) in enumerate(terms):
            value = field.mul(a, power(field, x, exponent))
            trace = value ^ field.mul(value, value)
            word |= trace << j
        expected[word] += 1
    result = histogram(len(terms), character)
    assert result == expected
    for modulus in (8, 32, 128):
        for w in range(modulus):
            weighted = sum(n * (w * (2-w))**2 *
                           __import__('math').prod((j+2)*w if mask>>j&1 else 1+(j+2)*(1-w)
                                                   for j in range(len(terms)))
                           for mask,n in result.items()) % modulus
            explicit = 0
            for mask,n in expected.items():
                factors = []
                for i in range(4):
                    row_bit = (i % 2)
                    factors.append(sum((w*x if row_bit else 1-w*x) for x in (0,1)))
                for j in range(len(terms)):
                    y = mask>>j & 1
                    factors.append(sum((1,j+2)[x]*(w*x if y else 1-w*x) for x in (0,1)))
                explicit += n * __import__('math').prod(factors)
            assert weighted == explicit % modulus
    print('GF(4) carry-cover histogram:', result, 'evaluations:', character.cache_info().currsize)

if __name__ == '__main__':
    check()
