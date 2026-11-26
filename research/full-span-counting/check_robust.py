#!/usr/bin/env python3
"""Exact implicit conflict search; exhaustive data used only inside the oracle and reference."""
from fractions import Fraction
from itertools import combinations, product
from random import Random


def solve(rows, p):
    matrix = [list(map(Fraction, row)) + [Fraction(1)] for row in rows]
    rank = 0
    pivots = []
    for i in range(p):
        k = next((k for k in range(rank, len(matrix)) if matrix[k][i]), None)
        if k is None:
            continue
        matrix[k], matrix[rank] = matrix[rank], matrix[k]
        pivot = matrix[rank][i]
        matrix[rank] = [v / pivot for v in matrix[rank]]
        for k, row in enumerate(matrix):
            if k != rank:
                scale = row[i]
                matrix[k] = [x - scale*y for x, y in zip(row, matrix[rank])]
        pivots.append(i)
        rank += 1
    if any(row[-1] for row in matrix[rank:]):
        return None
    c = [Fraction(0)] * p
    for i, row in zip(pivots, matrix):
        c[i] = row[-1]
    return c


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def conflict(gram, row, n, p, removed):
    witnesses = []
    while True:
        coeff = solve([row(z) for z in witnesses], p)
        if coeff is None:
            assert len(witnesses) <= p+1
            return witnesses, None
        vector = coeff + [-1]
        def energy(prefix):
            return dot(vector, [dot(r, vector) for r in gram(prefix, removed)])
        if not energy(()):
            return [], coeff
        prefix = ()
        for _ in range(n):
            prefix += (0 if energy(prefix+(0,)) else 1,)
        assert prefix not in witnesses and prefix not in removed
        witnesses.append(prefix)


def search(gram, row, n, p, removed, budget):
    bad, c = conflict(gram, row, n, p, removed)
    if c is not None:
        return removed, c
    if budget:
        for z in bad:
            solution = search(gram, row, n, p, removed | {z}, budget-1)
            if solution is not None:
                return solution
    return None


def main():
    rng = Random(61008)
    maximum = 0
    for case in range(32):
        n = 3
        p = 2 + case % 2
        domain = list(product(range(2), repeat=n))
        # h is the number of compatible hidden-core completions, Q counts violations.
        rules = [tuple(rng.choice((-1,0,1)) for _ in range(n)) for _ in range(5)]
        masks = [rng.randrange(1 << len(rules)) for _ in range(p)]
        h = {z:rng.randrange(5) for z in domain}
        features, Q = {}, {}
        for z in domain:
            matches = [all(v == -1 or x == v for x,v in zip(z,rule)) for rule in rules]
            Q[z] = sum(matches)
            features[z] = tuple(sum(v for j,v in enumerate(matches) if mask >> j & 1)
                                for mask in masks)
        def gram(prefix, removed):
            g = [[0]*(p+1) for _ in range(p+1)]
            for z in domain:
                if z[:len(prefix)] != prefix or z in removed:
                    continue
                v = features[z]+(1,)
                for i,j in product(range(p+1), repeat=2):
                    g[i][j] += Q[z]*h[z]*v[i]*v[j]
            return g
        eligible = [z for z in domain if h[z]*Q[z]]
        for minimum in range(len(eligible)+1):
            if any(solve([features[z] for z in eligible if z not in omitted],p) is not None
                   for omitted in combinations(eligible,minimum)):
                break
        for budget in range(minimum+1):
            result = search(gram, features.__getitem__, n,p,frozenset(),budget)
            assert (result is not None) == (budget == minimum)
        omitted,c = result
        corrected = sum(h[z]*dot(features[z],c) for z in domain)
        corrected += sum(h[z]*(1-dot(features[z],c)) for z in omitted)
        assert len(omitted) == minimum and corrected == sum(h[z] for z in eligible)
        maximum = max(maximum, minimum)
    print(f"32 random systems: minimum deletions and union counts agree; maximum optimum {maximum}.")


if __name__ == "__main__":
    main()
