"""Small exhaustive and seeded tests for sampled counter outputs."""
from itertools import product
from math import prod
from random import Random

def apply(matrix, vector):
    out = 0
    for j, row in enumerate(matrix):
        out |= ((row & vector).bit_count() & 1) << j
    return out

def multiply(left, right):
    columns = [apply(right, 1 << j) for j in range(len(right))]
    return tuple(sum(((row & col).bit_count() & 1) << j
                     for j, col in enumerate(columns)) for row in left)

def power(matrix, exponent):
    answer = tuple(1 << j for j in range(len(matrix)))
    while exponent:
        if exponent & 1:
            answer = multiply(answer, matrix)
        matrix = multiply(matrix, matrix)
        exponent >>= 1
    return answer

def main():
    rng = Random(947)
    checked = 0
    pairs = 0
    for n in range(1, 5):
        count = 1 << n
        half = count // 2
        clock = prod(2**j - 1 for j in range(1, half + 1))
        for width in range(1, half + 1):
            if width <= 3:
                matrices = product(range(1 << width), repeat=width)
            else:
                matrices = (tuple(rng.randrange(1 << width) for _ in range(width))
                            for _ in range(40))
            for matrix in matrices:
                # One matrix identity implies all address-pair equalities.
                warm = power(matrix, clock * count)
                shift = power(matrix, clock * half)
                assert multiply(warm, shift) == warm
                checked += 1
        jordan = tuple((1 << j) | ((1 << (j - 1)) if j else 0)
                       for j in range(half + 1))
        for i in range(count):
            tick = clock * (count + i)
            observed = (apply(power(jordan, tick), 1) >> half) & 1
            assert observed == ((tick >> (n - 1)) & 1)
            if i < half:
                assert ((tick + clock*half) & half) != (tick & half)
                pairs += 1
    print(f"{checked} matrix identities and {pairs} counter pairs passed")

if __name__ == "__main__":
    main()
