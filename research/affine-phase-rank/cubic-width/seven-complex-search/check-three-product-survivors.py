"""Exact small local check for the three product factors of a four-ray G2 list."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "g3-complex-conic-search"))
from search import stabs

# Gaussian integers in complex128: all operations below, apart from Fraction
# evaluation, are additions, products and conjugations of small integers.
# No linear algebra tolerances or floating division are used.
identity = np.eye(8, dtype=np.complex128)
indices = np.arange(8)
g = np.array([1] * 7 + [-1], dtype=np.complex128)
rays = np.array([[0 if j < 0 else 1j**j for j in row] for row in stabs()])
assert len(rays) == 1080


def signed_checks(a):
    result = []
    for x, z in product(range(8), repeat=2):
        phase = 1j ** ((x & z).bit_count())
        signs = np.array([(-1) ** ((i & z).bit_count()) for i in range(8)])
        pauli = phase * signs[:, None] * identity[indices ^ x]
        if np.array_equal(pauli @ a, a):
            result.append(pauli)
        elif np.array_equal(pauli @ a, -a):
            result.append(-pauli)
    assert len(result) == 8
    return result


def local_data(a):
    p = g - a
    codes = []
    counts = Counter()
    used_extra = set()
    for s, t in combinations(signed_checks(a), 2):
        projector4 = (identity + s) @ (identity + t)
        if np.trace(projector4) != 8 or any(np.array_equal(projector4, h) for h in codes):
            continue
        codes.append(projector4)
        outside = 4 * identity - projector4
        target = outside @ p
        pivot = next(i for i, val in enumerate(target) if val)
        for ray_id, e in enumerate(rays):
            actual = outside @ e
            if not actual[pivot] or not np.array_equal(actual * target[pivot],
                                                        target * actual[pivot]):
                continue
            denominator = actual[pivot]
            u_num = target[pivot] * e - denominator * p
            normalization = int((denominator.conjugate() * denominator * np.vdot(a, a)).real)
            parallel = np.vdot(a, u_num) * denominator.conjugate()
            real = Fraction(int(parallel.real), normalization)
            imag = Fraction(int(parallel.imag), normalization)
            perp_sq = Fraction(int(np.vdot(u_num, u_num).real), normalization) - real**2 - imag**2
            if perp_sq:  # (a,e,p) must be independent.
                assert ray_id not in used_extra
                used_extra.add(ray_id)
                counts[(real, imag, perp_sq)] += 1
    assert len(codes) == 7
    return counts


def main():
    for name, a, parallel, perp_sq in [
        ("plane", g * (indices < 4), 0, 1),
        ("point", -2 * (indices == 7), 1, 1),
        ("full",  g + 2 * (indices == 7), Fraction(1, 2), Fraction(1, 4)),
    ]:
        counts = local_data(a)
        assert set(counts) == {(parallel, 0, perp_sq)}
        print(name, sum(counts.values()), (str(parallel), str(perp_sq)))


if __name__ == "__main__":
    main()
