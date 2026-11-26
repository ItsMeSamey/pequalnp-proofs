"""Exhaustive small-matrix and randomized larger model-span checks."""
from random import Random
from solve import model_basis, symmetric_switch, witness


def models(rows):
    return {x for x in range(1 << len(rows))
            if all(not x >> i & 1 or (row & x).bit_count() % 2 == 0
                   for i, row in enumerate(rows))}


def check(rows):
    feasible = models(rows)
    try:
        basis = model_basis(rows)
    except ValueError:
        basis = None
    if basis is not None:
        span = {0}
        for vector in basis:
            assert vector in feasible and vector not in span
            span |= {x ^ vector for x in span}
        assert feasible <= span
    for marker in range(1 << len(rows)):
        if basis is None and marker and symmetric_switch(rows, marker) is None:
            continue
        valid = {x for x in feasible if (x & marker).bit_count() % 2}
        answer = witness(rows, marker)
        assert answer in valid if valid else answer is None


if __name__ == '__main__':
    for n in range(4):
        for code in range(1 << (n*n)):
            check([(code >> (i*n)) % (1 << n) for i in range(n)])
    rng = Random(9206)
    for _ in range(50):
        n = 7
        rows = [0] * n
        for i in range(n):
            for j in range(i + 1):
                if rng.randrange(2):
                    rows[i] |= 1 << j
                    if i // 3 == j // 3:
                        rows[j] |= 1 << i
        check(rows)
    print("All matrices through dimension 3 and 50 seven-variable cases passed.")
