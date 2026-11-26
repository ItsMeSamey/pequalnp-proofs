"""Exhaustively compare actual clause violations with the parity-fiber formula."""
from collections import Counter
from itertools import combinations, product
from math import comb


def label(word):
    a, b, c = word
    return a ^ (b & c)


WORDS = list(product(range(2), repeat=3))


def forbidden_clause(scope, values):
    # A forbidden 1 is tested by a negative literal, a forbidden 0 by a positive one.
    return tuple(-var if bit else var for var, bit in zip(scope, values))


def edge_clauses(vertices, twist):
    blocks = [tuple(range(3 * i + 1, 3 * i + 4)) for i in range(vertices)]
    for i, block in enumerate(blocks):
        scope = block + blocks[(i + 1) % vertices]
        sign = int(twist and i == 0)
        yield [forbidden_clause(scope, left + right)
               for left, right in product(WORDS, repeat=2)
               if label(left) ^ label(right) != sign]


def rank(vectors):
    basis = {}
    for vector in vectors:
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = vector
                break
            vector ^= basis[pivot]
    return len(basis)


def affine_rank(words):
    values = [sum(bit << i for i, bit in enumerate(word)) for word in words]
    return rank(value ^ values[0] for value in values)


def check(vertices, twist):
    edges = list(edge_clauses(vertices, twist))
    assert all(len(clauses) == 32 for clauses in edges)
    histogram, syndrome_counts = Counter(), Counter()
    for bits in product(range(2), repeat=3 * vertices):
        # Inspect each literal of the generated CNF. The label function is not
        # consulted during evaluation.
        true_literals = {i if bit else -i for i, bit in enumerate(bits, 1)}
        errors = tuple(sum(true_literals.isdisjoint(clause) for clause in clauses)
                       for clauses in edges)
        assert max(errors) <= 1
        histogram[sum(errors)] += 1
        syndrome_counts[errors] += 1
    fiber = 2 * 4 ** vertices
    expected = {k: comb(vertices, k) * fiber for k in range(twist, vertices + 1, 2)}
    assert dict(histogram) == expected
    assert len(syndrome_counts) == 2 ** (vertices - 1)
    assert set(syndrome_counts.values()) == {fiber}
    for size in range(vertices):
        for coords in combinations(range(vertices), size):
            projected = Counter()
            for syndrome, count in syndrome_counts.items():
                projected[tuple(syndrome[i] for i in coords)] += count
            assert len(projected) == 2 ** size
            assert set(projected.values()) == {8 ** vertices // 2 ** size}
        moment = sum(comb(k, size) * count for k, count in histogram.items())
        assert 2 ** size * moment == 8 ** vertices * comb(vertices, size)
    return dict(sorted(histogram.items()))


if __name__ == "__main__":
    for t in range(2):
        assert affine_rank([w for w in WORDS if label(w) == t]) == 3
        assert affine_rank([u + v for u, v in product(WORDS, repeat=2)
                            if label(u) ^ label(v) == t]) == 6
    for n in (3, 4, 5):
        for odd in range(2):
            print(f"n={n}, twist={odd}, violation counts={check(n, odd)}")
