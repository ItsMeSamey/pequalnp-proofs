"""Verify native Boolean wiring and count decoding on all small open permutations."""
from collections import defaultdict
from itertools import permutations, product
from math import factorial


def skip(p, source, hidden):
    x = p[source]
    while x in hidden:
        x = p[x]
    return x


def verify_gadgets():
    for g in [(0, 1, 2), (1, 2, 0)]:
        result = [skip(g, x, {2}) for x in range(2)]
        assert result == ([0, 1] if g[0] == 0 else [1, 0])
        assert skip(g, 0, {1, 2}) == 0
    for x, y in product(range(2), repeat=2):
        left = (2, 1, 0) if x else (0, 1, 2)
        right = (0, 2, 1) if y else (0, 1, 2)
        perm = [right[i] for i in left]
        assert skip(perm, 0, {2}) == x * y


def shuffle_counts(p, d, modulus):
    counts = {tuple(range(p)): 1}
    used = 0
    for j in range(2, p + 1):
        for i in range(j, 1, -1):
            r = (2**d * (i - 1) * pow(i, -1, modulus)) % modulus
            successes = 0
            for bit in range(d):
                successes += ((r >> bit) & 1) * 2**bit
            assert successes == r
            next_counts = defaultdict(int)
            for ordering, count in counts.items():
                swapped = list(ordering)
                swapped[i - 2], swapped[i - 1] = swapped[i - 1], swapped[i - 2]
                next_counts[tuple(swapped)] += successes * count
                next_counts[ordering] += (2**d - successes) * count
            counts = next_counts
            used += d
    assert sum(counts.values()) == 2**used
    return counts, used


def check(p, n):
    modulus = 2**(n + 2) * factorial(p) + 1
    counts, used = shuffle_counts(p, modulus.bit_length(), modulus)
    # s=t=0 and the spare channel has label p.
    for old in permutations(range(p)):
        h = old + (p,)
        z = 0
        for remainder, weight in counts.items():
            k = (p,) + remainder
            succ = [k[y] for y in h]
            x = succ[0]
            while x != 0 and x != p:
                x = succ[x]
            if x == p:
                z += weight
        # All 2^n masks have the specified permutation in each test.
        # Linearity then covers arbitrary multisets of these permutations.
        z *= 2**(n + 2)
        total_bits = n + used + 2
        decoded = 2**n * (2 * z * pow(2**total_bits, -1, modulus) - 1)
        assert decoded % modulus == (2**n if old[0] == 0 else 0)


if __name__ == "__main__":
    verify_gadgets()
    for p, n in product(range(1, 6), (0, 1, 5)):
        check(p, n)
    print("Checked the fair gate, AND, marking pad, and every open permutation through p=5.")
