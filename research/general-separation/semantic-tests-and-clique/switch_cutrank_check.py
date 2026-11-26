"""Finite checks of binary Pfaffian cut profiles and prefix compression."""
import itertools
import random


def basis_add(basis, value):
    while value:
        pivot = value.bit_length() - 1
        if pivot not in basis:
            basis[pivot] = value
            return True
        value ^= basis[pivot]
    return False


def principal_pf(matrix, selected):
    # On an alternating binary matrix, the Pfaffian equals its determinant.
    rows = {}
    return int(all(basis_add(rows, matrix[i] & selected)
                   for i in range(len(matrix)) if selected >> i & 1))


def cut_factors(matrix, split):
    # Track the actual right-side vectors and each left row's coordinates.
    vectors = []
    pivots = {}
    left = []
    for row in matrix[:split]:
        v, coords = row >> split, 0
        while v:
            j = v.bit_length() - 1
            if j not in pivots:
                label = 1 << len(vectors)
                pivots[j] = (v, label)
                vectors.append(v)
            vec, label = pivots[j]
            v ^= vec
            coords ^= label
        left.append(coords)
    right = [sum(((v >> j) & 1) << i for i, v in enumerate(vectors))
             for j in range(len(matrix)-split)]
    return left, right, len(vectors)


def profile(matrix, indexes, mask, factor, r):
    n = len(indexes)
    rows = [sum(((matrix[i] >> j) & 1) << b for b, j in enumerate(indexes))
            | (factor[a] << n) for a, i in enumerate(indexes)]
    rows += [sum(((a >> i) & 1) << b for b, a in enumerate(factor))
             for i in range(r)]
    return sum(principal_pf(rows, mask | (t << n)) << t for t in range(1 << r))


def compressed(matrix, groups):
    survivors = [0]
    end = 0
    for size, twist in groups:
        mask = (1 << size) - 1
        choices = [b | (a << end) for b in survivors for a in (twist, twist ^ mask)]
        end += size
        u, _, r = cut_factors(matrix, end)
        basis, survivors = {}, []
        for b in choices:
            if basis_add(basis, profile(matrix, range(end), b, u, r)):
                survivors.append(b)
    return bool(survivors)


if __name__ == "__main__":
    rng = random.Random(73521)
    for trial in range(400):
        n = rng.randrange(2, 13)
        matrix = [0]*n
        for i, j in itertools.combinations(range(n), 2):
            if rng.randrange(2):
                matrix[i] |= 1 << j
                matrix[j] |= 1 << i
        s = rng.randrange(n+1)
        u, v, r = cut_factors(matrix, s)
        assert all(((u[i] & v[j]).bit_count() % 2) == (matrix[i] >> (s+j) & 1)
                   for i in range(s) for j in range(n-s))
        a, b = rng.randrange(1 << s), rng.randrange(1 << (n-s))
        p = profile(matrix, range(s), a, u, r)
        q = profile(matrix, range(s,n), b, v, r)
        assert (p & q).bit_count() % 2 == principal_pf(matrix, a | (b << s))
        groups, end, masks = [], 0, [0]
        while end < n:
            size = rng.randrange(1, min(4,n-end)+1)
            full = (1 << size)-1
            twist = rng.randrange(full+1)
            groups.append((size, twist))
            masks = [b | (a << end) for b in masks for a in (twist, twist ^ full)]
            end += size
        assert compressed(matrix, groups) == any(principal_pf(matrix,b) for b in masks)
    print("400 factorization, Pfaffian gluing, and grouped feasibility tests passed")
