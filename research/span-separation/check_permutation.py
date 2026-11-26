"""Check Walsh-projected signed determinant coefficients against exhaustive coloring."""

from itertools import combinations, permutations
from math import prod
from random import Random


def projected_coefficients(n, k, labels, target, edges):
    """Return the integer coefficients before dividing the Walsh sum by 2**k."""
    terms = []
    for perm in permutations(range(n)):
        moved = [i for i in range(n) if perm[i] != i]
        used = [tuple(sorted((i, perm[i]))) for i in moved]
        if any(edge not in edges for edge in used):
            continue
        difference = prod(edges[edge] for edge in used) - 1
        if difference:
            inversions = sum(perm[i] > perm[j] for i, j in combinations(range(n), 2))
            fixed = [i for i in range(n) if i == perm[i]]
            terms.append((fixed, difference * (-1) ** inversions))

    coefficients = [0] * (n + 1)
    for character in range(1 << k):
        target_sign = (-1) ** ((character & target).bit_count() % 2)
        for fixed, weight in terms:
            # A fixed diagonal factor is zero or two.
            if all((character & labels[i]).bit_count() % 2 == 0 for i in fixed):
                coefficients[n - len(fixed)] += target_sign * weight * (1 << len(fixed))
    return coefficients


def brute_feasible(n, labels, target, edges):
    for flipped in range(1 << n):
        syndrome = 0
        for i, label in enumerate(labels):
            if flipped & (1 << i):
                syndrome ^= label
        if syndrome != target:
            continue
        retained = [(i, j, sign) for (i, j), sign in edges.items()
                    if not (flipped & ((1 << i) | (1 << j)))]
        # A graph is balanced precisely when all its edge signs admit potentials.
        balanced = any(
            all(((potential >> i ^ potential >> j) & 1) == (sign == -1)
                for i, j, sign in retained)
            for potential in range(1 << n)
        )
        if not balanced:
            return True
    return False


def main():
    rng = Random(713)
    for case in range(400):
        n = rng.randrange(3, 7)
        k = rng.randrange(1, 4)
        labels = [rng.randrange(1 << k) for _ in range(n)]
        target = rng.randrange(1 << k)
        edges = {edge: rng.choice((-1, 1)) for edge in combinations(range(n), 2)
                 if rng.random() < 0.65}
        coeff = projected_coefficients(n, k, labels, target, edges)
        if any(coeff) != brute_feasible(n, labels, target, edges):
            raise AssertionError((case, n, k, labels, target, edges, coeff))
    print("400 signed determinant checks passed (seed 713)")


if __name__ == "__main__":
    main()
