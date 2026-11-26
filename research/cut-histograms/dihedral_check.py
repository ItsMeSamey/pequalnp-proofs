#!/usr/bin/env python3
"""Check both affine-score/dihedral-word reductions by evaluating assignments."""
from itertools import product
from random import Random


def multiply(left, right, m):
    a, b = left
    c, d = right
    return ((a + (-1 if b else 1) * c) % m, b ^ d)


def invert(g, m):
    a, b = g
    return (a if b else -a) % m, b


def inverse_word(word):
    return [(kind, value, -sign) for kind, value, sign in reversed(word)]


def evaluate(word, inputs, m):
    acc = (0, 0)
    for kind, value, sign in word:
        g = inputs[value] if kind == 'x' else value
        acc = multiply(acc, g if sign == 1 else invert(g, m), m)
    return acc


def decode(mask, bits):
    return (mask & bits).bit_count() % 2


def score_word(terms, target, m):
    half = pow(2, -1, m)
    word = []
    for mask, offset, weight in terms:
        selector = [('c', (0, offset), 1)]
        selector.extend(('x', j, 1) for j in range(mask.bit_length()) if mask >> j & 1)
        word.extend(selector + [('c', (-weight * half % m, 0), 1)]
                    + inverse_word(selector) + [('c', (weight * half % m, 0), 1)])
    return word + [('c', (-target % m, 0), 1)]


def score_from_word(word, m, n):
    # Use a modular Fourier transform for each independent local truth table.
    width = (m - 1).bit_length()
    prefix, offset = 0, 0
    constant, weights = 0, {}
    for kind, value, sign in word:
        if kind == 'x':
            flip = 1 << value
            rotations = [1 << (n + value * width + j) for j in range(width)]
            forms = [(prefix, offset), (flip, 0)] + [(mask, 0) for mask in rotations]
            def lut(z):
                prefix_sign, reflection = z & 1, z >> 1 & 1
                rotation = (z >> 2) % m
                signed_rotation = -rotation if sign == -1 and not reflection else rotation
                return -signed_rotation if prefix_sign else signed_rotation
        else:
            rotation, reflection = value
            signed_rotation = -rotation if sign == -1 and not reflection else rotation
            forms = [(prefix, offset)]
            def lut(z):
                return -signed_rotation if z else signed_rotation
        size = 1 << len(forms)
        scale = pow(size, -1, m)
        for subset in range(size):
            coeff = scale * sum((-1) ** decode(subset, z) * lut(z) for z in range(size)) % m
            mask, shift = 0, 0
            for j, (form, c) in enumerate(forms):
                if subset >> j & 1:
                    mask ^= form
                    shift ^= c
            if shift:
                coeff = -coeff
            constant += coeff
            if mask:
                weights[mask] = (weights.get(mask, 0) - 2 * coeff) % m
        if kind == 'x':
            prefix ^= flip
        else:
            offset ^= reflection
    return constant % m, weights, prefix, offset


def check():
    rng = Random(17491)
    forward = reverse = 0
    for m in (3, 5, 9, 15, 21):
        group = list(product(range(m), range(2)))
        width = (m - 1).bit_length()
        for _ in range(5):
            terms = [(mask, rng.randrange(2), rng.randrange(-m, 2*m)) for mask in range(4)]
            target = rng.randrange(m)
            word = score_word(terms, target, m)
            for inputs in product(group, repeat=2):
                bits = inputs[0][1] | inputs[1][1] << 1
                score = sum(w * (decode(mask, bits) ^ c) for mask, c, w in terms)
                assert evaluate(word, inputs, m) == ((score-target) % m, 0)
                forward += 1
        words = [[], [('x', 0, -1)], [('c', (2, 1), 1), ('x', 0, -1)],
                 [('x', 1, 1), ('x', 0, -1), ('x', 1, -1), ('c', (1, 1), -1)]]
        for _ in range(4):
            words.append([('x', rng.randrange(2), rng.choice((-1, 1))) if rng.randrange(2)
                          else ('c', rng.choice(group), rng.choice((-1, 1))) for _ in range(6)])
        for word in words:
            constant, weights, prefix, offset = score_from_word(word, m, 2)
            for bits in range(1 << (2 + 2 * width)):
                inputs = [((bits >> (2+j*width) & ((1 << width)-1)) % m, bits >> j & 1)
                          for j in range(2)]
                actual = evaluate(word, inputs, m)
                rotation = (constant + sum(w * decode(mask, bits) for mask,w in weights.items())) % m
                assert actual == (rotation, decode(prefix, bits) ^ offset)
                reverse += 1
    print(f'passed {forward} forward and {reverse} reverse assignment checks')


if __name__ == '__main__':
    check()
