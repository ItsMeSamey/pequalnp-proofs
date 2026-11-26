"""Finite checks for the bounded-cycle-rank witness reduction for binary lifts."""
from functools import reduce
from itertools import combinations
from operator import xor
from random import Random


def bits(mask):
    return [v for v in range(mask.bit_length()) if mask >> v & 1]


def add(basis, x):
    for v in basis:
        x = min(x, x ^ v)
    if not x:
        return False
    basis.append(x)
    basis.sort(reverse=True)
    return True


def contains(basis, x):
    return not add(basis.copy(), x)


def label(vertices, markers):
    return reduce(xor, (markers[v] for v in vertices), 0)


def brute(n, edges, markers, syndrome, target):
    for coloring in range(1 << n):
        if label(bits(coloring), markers) != syndrome:
            continue
        basis = []
        for i, j, sign in edges:
            if (coloring >> i ^ coloring >> j) & 1 == 0:
                add(basis, (1 << i) ^ (1 << j) ^ (sign << n))
        if contains(basis, target << n):
            return True
    return False


def reduced(n, edges, markers, syndrome, target, dimensions, constraints):
    for mask in range(1, 1 << len(edges)):
        graph = [[] for _ in range(n)]
        sign_sum = 0
        for e in bits(mask):
            i, j, sign = edges[e]
            graph[i].append(j)
            graph[j].append(i)
            sign_sum ^= sign
        if sign_sum != target or any(len(nb) % 2 for nb in graph):
            continue
        used = {i for i, nb in enumerate(graph) if nb}
        unseen = used.copy()
        components = []
        while unseen:
            start = unseen.pop()
            stack, component = [start], [start]
            while stack:
                for v in graph[stack.pop()]:
                    if v in unseen:
                        unseen.remove(v)
                        stack.append(v)
                        component.append(v)
            components.append(component)
        rank = mask.bit_count() - len(used) + len(components)
        if rank > dimensions:
            continue
        outside = set(range(n)) - used
        possible = {label(s, markers) for t in range(min(constraints, len(outside)) + 1)
                    for s in combinations(outside, t)}
        for pattern in range(1 << len(components)):
            chosen = (v for i in bits(pattern) for v in components[i])
            if syndrome ^ label(chosen, markers) in possible:
                return True
    return False


def check_mod_four(vertices, markers, constraints):
    for j in range(constraints):
        weights = [(markers[v] >> j) & 1 for v in vertices]
        edge_sum = sum(a + b for a, b in zip(weights, weights[1:]))
        endpoints = weights[0] + weights[-1]
        assert (edge_sum - endpoints) % 4 == 2 * (sum(weights[1:-1]) % 2)


def main():
    rng = Random(6721)
    for iteration in range(500):
        n, d, h = rng.randint(2, 7), rng.randint(1, 4), rng.randint(1, 4)
        edges = [(rng.randrange(n), rng.randrange(n), rng.randrange(1 << d))
                 for _ in range(rng.randrange(10))]
        marks = [rng.randrange(1 << h) for _ in range(n)]
        s, b = rng.randrange(1 << h), rng.randrange(1, 1 << d)
        expected = brute(n, edges, marks, s, b)
        assert reduced(n, edges, marks, s, b, d, h) == expected, iteration
        check_mod_four(rng.sample(range(n), rng.randint(2, n)), marks, h)
    # Two loops of different labels must be assigned opposite colors.
    edges = [(0, 0, 1), (1, 1, 2)]
    assert brute(2, edges, [1, 1], 1, 3)
    assert reduced(2, edges, [1, 1], 1, 3, 2, 1)
    print("500 higher-lift reductions and path-weight checks passed, plus two-cycle fixture")


if __name__ == "__main__":
    main()
