"""Check reciprocal kernels and the full sign table at order four."""
from itertools import combinations, product

def check(q, modulus):
    def mul(x, y):
        value = 0
        while y:
            if y & 1:
                value ^= x
            y >>= 1
            x <<= 1
            if x & q:
                x ^= modulus
        return value
    inv = [0] + [next(y for y in range(1, q) if mul(x, y) == 1)
                 for x in range(1, q)]
    def rank(rows):
        basis = {}
        for original in rows:
            row = original.copy()
            for j in sorted(basis):
                scale = row[j]
                row = [a ^ mul(scale, b) for a, b in zip(row, basis[j])]
            pivot = next((j for j, x in enumerate(row) if x), None)
            if pivot is not None:
                basis[pivot] = [mul(inv[row[pivot]], a) for a in row]
        return len(basis)
    kernel = [[inv[x ^ y] for y in range(q)] for x in range(q)]
    assert rank(kernel) == q // 2
    checks = 0
    for size in range(1, q // 2 + 1):
        for left in combinations(range(q), size):
            rest = sorted(set(range(q)) - set(left))
            for right in combinations(rest, size):
                assert rank([[kernel[i][j] for j in right] for i in left]) == size
                checks += 1
    print(f"q={q}, kernel rank {q//2}, {checks} disjoint square minors")
    if q != 4:
        return
    def phase(word):
        e = 0
        for i, j in combinations(range(q), 2):
            e ^= mul(kernel[i][j], mul(word[i], word[j]))
        trace = e ^ mul(e, e)
        assert trace in (0, 1)
        return 1 - 2*trace
    counts = 0
    for owners in product(range(3), repeat=q):
        left, right, fixed = ([i for i in range(q) if owners[i] == s] for s in range(3))
        if not 0 < len(left) <= len(right):
            continue
        for setting in product(range(q), repeat=len(fixed)):
            rows = []
            for a in product(range(q), repeat=len(left)):
                values = []
                for b in product(range(q), repeat=len(right)):
                    values.append(phase(dict(zip(left + right + fixed, a + b + setting))))
                rows.append(values)
            assert all(sum(x*y for x, y in zip(u, v)) == 0
                       for u, v in combinations(rows, 2))
            counts += 1
    print(f"q=4, {counts} fixed-group signed tables checked")

if __name__ == "__main__":
    check(4, 0b111)
    check(8, 0b1011)
