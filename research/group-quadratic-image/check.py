"""Finite checks for the low-block reconstruction and modular type compression."""
from itertools import combinations, product
from random import Random


def image_columns(matrix, rows, columns, modulus):
    zero = (0,) * len(rows)
    result = {zero}
    for j in columns:
        col = [matrix[i][j] for i in rows]
        result = {tuple((x + k*y) % modulus for x, y in zip(v, col))
                  for v in result for k in range(modulus)}
    return result


def grow(matrix, modulus):
    rows, cols = [], []
    others = set(range(len(matrix)))
    image_size = 1
    while len(others) > 1:
        choice = None
        for i in sorted(others):
            for j in sorted(others - {i}):
                size = len(image_columns(matrix, rows + [i], cols + [j], modulus))
                if size > image_size:
                    choice = (i, j, size)
                    break
            if choice:
                break
        if not choice:
            break
        i, j, new_size = choice
        assert new_size % image_size == 0 and new_size <= image_size * modulus**2
        image_size = new_size
        rows.append(i)
        cols.append(j)
        others -= {i, j}
    return rows, cols, sorted(others)


def scalar_score(matrix, linear, x, modulus):
    return (sum(linear[i] for i in x)
            + sum(matrix[i][j] for i, j in combinations(x, 2))) % modulus


def verify_low(modulus, n, rng):
    w = [[0]*n for _ in range(n)]
    for i, j in combinations(range(n), 2):
        w[i][j] = w[j][i] = rng.randrange(modulus)
    lin = [rng.randrange(modulus) for _ in range(n)]
    rows, cols, rest = grow(w, modulus)
    assert len(image_columns(w, rows, cols, modulus)) == len(image_columns(w, cols, rows, modulus))
    if len(rest) <= 1:
        return
    # Reconstruct every factor g_i on H directly by its value on representatives.
    reps = {}
    for coeff in product(range(modulus), repeat=len(cols)):
        v = tuple(sum(a * w[j][i] for i, a in zip(cols, coeff)) % modulus for j in rows)
        reps.setdefault(v, coeff)
    for i in rest:
        for j in rest:
            if i == j:
                continue
            v = tuple(w[h][j] for h in rows)
            assert v in reps
            a = reps[v]
            assert w[i][j] == sum(c*w[i][k] for c, k in zip(a, cols)) % modulus
    pin = rows + cols
    group_by_signature = {}
    for mask in range(1 << n):
        x = {i for i in range(n) if mask >> i & 1}
        counts = {}
        for i in x.intersection(rest):
            tp = (lin[i], tuple(w[i][j] for j in pin))
            counts[tp] = (counts.get(tp, 0) + 1) % (2 * modulus)
        key = (frozenset(x.intersection(pin)), frozenset((k,v) for k,v in counts.items() if v))
        val = scalar_score(w, lin, x, modulus)
        assert group_by_signature.setdefault(key, val) == val


def repeated_types(modulus, rng):
    types = 3
    n = 2 * modulus + 3
    l = [rng.randrange(modulus) for _ in range(types)]
    w = [[0]*types for _ in range(types)]
    for i in range(types):
        for j in range(i, types):
            w[i][j] = w[j][i] = rng.randrange(modulus)
    def value(counts):
        linear = sum(a*b for a,b in zip(counts, l))
        within = sum(a*(a-1)//2*w[i][i] for i,a in enumerate(counts))
        between = sum(counts[i]*counts[j]*w[i][j] for i,j in combinations(range(types),2))
        return (linear + within + between) % modulus
    for counts in product(range(n+1), repeat=types):
        assert value(counts) == value([x % (2*modulus) for x in counts])


if __name__ == '__main__':
    rng = Random(124850)
    cases = 0
    for m in (2, 3, 4, 5, 6, 8, 9, 10, 12):
        repeated_types(m, rng)
        for _ in range(60):
            verify_low(m, rng.randrange(2, 9), rng)
            cases += 1
    print(f'{cases} modular Schur and signature checks; nine count-periodicity tests')
