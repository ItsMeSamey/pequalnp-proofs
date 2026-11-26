#!/usr/bin/env python3
"""Exhaustive small-case tests for GF(2) truth trains and field path counting."""
from itertools import product
from math import comb, isqrt
from random import Random

# GF(256), in the polynomial basis modulo X^8+X^4+X^3+X+1.
def mul(a, b):
    answer = 0
    while b:
        if b & 1:
            answer ^= a
        a <<= 1
        if a & 256:
            a ^= 0x11b
        b >>= 1
    return answer


def power(a, k):
    value = 1
    while k:
        if k & 1:
            value = mul(value, a)
        a = mul(a, a)
        k >>= 1
    return value


def make_train(tables, scope):
    # Each bit of a row is the truth value at one suffix assignment.
    rows = [sum(bit << i for i, bit in enumerate(tables))]
    layers = []
    for idx, var in enumerate(scope):
        half = 1 << (len(scope) - idx - 1)
        basis, pivots, transitions = [], {}, []
        for row in rows:
            edge = []
            for local in (0, 1):
                residual = (row >> (half * local)) & ((1 << half) - 1)
                combination = 0
                while residual:
                    pivot = residual.bit_length() - 1
                    if pivot not in pivots:
                        pivots[pivot] = len(basis)
                        basis.append(residual)
                    i = pivots[pivot]
                    combination ^= 1 << i
                    residual ^= basis[i]
                edge.append(combination)
            transitions.append(edge)
        layers.append((var, transitions))
        rows = basis
    assert rows in ([], [1])
    return layers


def train_paths(train, assignment):
    # Count accepting paths as ordinary integers; reduce only at the end.
    states = {0: 1}
    for var, transitions in train:
        after = {}
        for i, count in states.items():
            mask = transitions[i][assignment[var]]
            for j in range(mask.bit_length()):
                if mask >> j & 1:
                    after[j] = after.get(j, 0) + count
        states = after
    return states.get(0, 0)


def field_paths(assignment, weights):
    states = [1] + [0] * 7
    for start in range(0, len(weights), 2):
        factor = 1
        for i in range(start, min(len(weights), start + 2)):
            if assignment[i]:
                factor = mul(factor, weights[i])
        after = [0] * 8
        for src, count in enumerate(states):
            mask = mul(factor, 1 << src)
            for dst in range(8):
                if mask >> dst & 1:
                    after[dst] += count
        states = after
    return states


def weighted(assignments, weights):
    coords = [0] * 8
    for assignment, paths in assignments:
        for dst, count in enumerate(field_paths(assignment, weights)):
            coords[dst] += paths * count
    return sum((bit & 1) << j for j, bit in enumerate(coords))


def interpolate(values):
    # Incremental interpolation in the monomial basis at distinct byte nodes.
    coeff = [0] * len(values)
    basis = [1]
    for x, y in enumerate(values):
        def evaluate(poly):
            v = 0
            for c in reversed(poly):
                v = mul(x, v) ^ c
            return v
        scale = mul(y ^ evaluate(coeff), power(evaluate(basis), 254))
        for j, c in enumerate(basis):
            coeff[j] ^= mul(scale, c)
        basis = [mul(x, c) ^ prev for c, prev in zip(basis + [0], [0] + basis)]
    return coeff


def main():
    rng = Random(39821)
    cases = 0
    for n in range(2, 8):
        for repeat in range(5):
            factors = []
            for _ in range(3):
                scope = rng.sample(range(n), rng.randint(1, n))
                table = [rng.randrange(2) for _ in range(1 << len(scope))]
                factors.append((scope, table, make_train(table, scope)))
            assignments, models = [], []
            for x in product(range(2), repeat=n):
                paths = 1
                for scope, table, train in factors:
                    index = sum(x[i] << j for j, i in enumerate(reversed(scope)))
                    count = train_paths(train, x)
                    assert count % 2 == table[index]
                    paths *= count
                assignments.append((x, paths))
                if paths & 1:
                    models.append(x)
            for _ in range(4):
                weights = [rng.randrange(256) for _ in range(n)]
                expected = 0
                for x in models:
                    term = 1
                    for bit, weight in zip(x, weights):
                        if bit:
                            term = mul(term, weight)
                    expected ^= term
                assert weighted(assignments, weights) == expected
                cases += 1

    # Two binary codes 0 and 6 collide in BOTH of the first two primes.
    n, bound = 3, 2
    primes = [p for p in range(2, 20) if all(p % d for d in range(2, isqrt(p) + 1))]
    primes = primes[:1 + n * comb(bound, 2)]
    supports = []
    table = [int(i in (0, 3)) for i in range(8)]
    train = make_train(table, range(n))
    assignments = [(x, train_paths(train, x)) for x in product(range(2), repeat=n)]
    for p in primes:
        powers = [pow(2, i, p) for i in range(n)]
        degree = sum(powers)
        values = [weighted(assignments, [power(y, e) for e in powers])
                  for y in range(degree + 1)]
        coeff = interpolate(values)
        supports.append(sum(c != 0 for c in coeff))
    assert max(supports) == bound
    # Raw substituted degrees are reduced per coordinate only; collisions
    # modulo p can split in ordinary interpolation. This example splits.
    assert supports == [0, 2, 2, 2], supports
    print(f"{cases} exact weighted comparisons passed; sparse interpolation primes {primes}, supports {supports}")


if __name__ == "__main__":
    main()
