"""Finite checks of the theta-independent multiplication results."""
from itertools import combinations
from math import comb
from random import Random


def walsh_sums(bits):
    values = [1 - 2 * bit for bit in bits]
    step = 1
    while step < len(values):
        for base in range(0, len(values), 2 * step):
            for i in range(base, base + step):
                a, b = values[i], values[i + step]
                values[i], values[i + step] = a + b, a - b
        step *= 2
    return values


def check_phases(d, t, threshold, trials, seed):
    block_bits = (3 if threshold else 2) * d
    inputs = block_bits * t
    count = 1 << inputs
    local = (1 << block_bits) - 1
    half = (1 << d) - 1
    def positive(x):
        if threshold:
            return x.bit_count() >= d + 1
        return ((x & half) == half) != ((x >> d) == half)
    bits = [any(positive((i >> (block_bits * j)) & local) for j in range(t))
            for i in range(count)]
    monomials = [sum(1 << i for i in chosen) for size in range(d)
                 for chosen in combinations(range(inputs), size)]
    rng = Random(seed)
    for _ in range(trials):
        phase = [0] * count
        for mask in monomials:
            phase[mask] = rng.randrange(2)
        for i in range(inputs):
            jump = 1 << i
            for block in range(0, count, 2 * jump):
                for x in range(block + jump, block + 2 * jump):
                    phase[x] ^= phase[x - jump]
        walsh = walsh_sums([bit ^ p for bit, p in zip(bits, phase)])
        assert all(abs(value) & -abs(value) == 1 << (t + 1) for value in walsh)


def check_thresholds():
    for q in [2, 4, 8, 16, 32, 64]:
        m = 3 * q
        assert sum(comb(m, i) for i in range(q + 1)) % 4 == 2
        degrees = [j for j in range(q + 1, m + 1) if comb(j - 1, q) % 2]
        assert degrees == list(range(q + 1, 2 * q + 1))
    # Directly count largest cliques for all 64 assignments on 12 vertices.
    for x in range(64):
        masks = [0]
        for pair in range(6):
            u, v = 1 << (2 * pair), 1 << (2 * pair + 1)
            options = [u, v, u | v] if x >> pair & 1 else [u, v]
            masks = [mask | choice for mask in masks for choice in options]
        assert max(mask.bit_count() for mask in masks) == 6 + x.bit_count()


if __name__ == "__main__":
    check_thresholds()
    for d, t, threshold, trials in [(2, 2, False, 16), (3, 2, False, 32),
                                     (2, 2, True, 16), (4, 1, True, 32)]:
        check_phases(d, t, threshold, trials, 63917 + d + t + threshold)
    print("96 seeded full Walsh spectra checked, including cross-block quadratics")
    print("6 threshold orders checked; all 64 free-edge settings in the smallest graph")
