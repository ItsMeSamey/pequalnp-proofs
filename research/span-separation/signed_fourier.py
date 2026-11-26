"""Deterministic Fourier decision test for a negative cycle avoiding a given XOR syndrome."""
from math import factorial


def determinant(matrix):
    data = [row[:] for row in matrix]
    sign = previous = 1
    for i in range(len(data)-1):
        pivot_row = next((j for j in range(i, len(data)) if data[j][i]), None)
        if pivot_row is None:
            return 0
        if pivot_row != i:
            data[i], data[pivot_row] = data[pivot_row], data[i]
            sign = -sign
        pivot = data[i][i]
        for j in range(i+1, len(data)):
            for h in range(i+1, len(data)):
                data[j][h] = (data[j][h]*pivot - data[j][i]*data[i][h]) // previous
            data[j][i] = 0
        previous = pivot
    return sign * data[-1][-1] if data else 1


def feasible(labels, dimension, rhs, edges):
    """Edges (i,j,negative_bit); labels[i] and rhs are binary-packed syndromes."""
    n = len(labels)
    size = n + 2 * len(edges)
    if not edges:
        return False
    # Each polynomial coefficient has magnitude ≤ 2^(dimension+n+1) * size!.
    point = (factorial(size) << (dimension+n+1)) + 2
    unsigned = [[0]*size for _ in range(size)]
    signed = [[0]*size for _ in range(size)]
    for slot, (i, j, negative) in enumerate(edges):
        a, b = n+2*slot, n+2*slot+1
        for start, end, bit in [(i,a,negative), (a,b,0), (b,j,0)]:
            unsigned[start][end] = unsigned[end][start] = point
            signed[start][end] = signed[end][start] = -point if bit else point
    total = 0
    for character in range(1 << dimension):
        for i in range(size):
            value = 1 if i >= n else 2*(1 - ((character & labels[i]).bit_count() % 2))
            signed[i][i] = unsigned[i][i] = value
        term = determinant(signed) - determinant(unsigned)
        total += -term if (character & rhs).bit_count() % 2 else term
    return bool(total)


if __name__ == '__main__':
    from random import Random
    rng = Random(921)
    for _ in range(150):
        n = rng.randrange(1, 6)
        d = rng.randrange(1, 4)
        labels = [rng.randrange(1 << d) for _ in range(n)]
        rhs = rng.randrange(1 << d)
        edges = [(rng.randrange(n), rng.randrange(n), rng.randrange(2))
                 for _ in range(rng.randrange(6))]
        wanted = False
        for excluded in range(1 << n):
            syndrome = 0
            for i in range(n):
                if excluded >> i & 1:
                    syndrome ^= labels[i]
            if syndrome != rhs:
                continue
            rest = [(i,j,s) for i,j,s in edges if not (excluded >> i & 1 or excluded >> j & 1)]
            balanced = any(all(((h >> i) ^ (h >> j)) & 1 == s for i,j,s in rest)
                           for h in range(1 << n))
            if not balanced:
                wanted = True
                break
        assert feasible(labels,d,rhs,edges) == wanted
    print("150 exact determinant decisions matched brute force, with loops and parallel edges")
