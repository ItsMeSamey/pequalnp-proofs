"""Find invertible diagonal completions of symmetric binary D at a prescribed syndrome."""
from itertools import combinations


def invertible(rows):
    basis = {}
    for row in rows:
        while row:
            i = row.bit_length() - 1
            if i not in basis:
                basis[i] = row
                break
            row ^= basis[i]
        else:
            return False
    return True


def solve(rows, labels, target):
    """labels[i] is column i of H as a bit mask. Return packed t, or None."""
    n = len(rows)
    if len(labels) != n or target < 0 or any(x < 0 for x in labels):
        raise ValueError("invalid syndrome data")
    if any(not 0 <= row < 1 << n for row in rows):
        raise ValueError("invalid matrix")
    if any(((rows[i] >> j) ^ (rows[j] >> i)) & 1 for i, j in combinations(range(n), 2)):
        raise ValueError("expected symmetric matrix")
    # Border determinants differ by the previous nonsingular leading determinant.
    t = 0
    base = list(rows)
    for i in range(n):
        mask = (2 << i) - 1
        if not invertible([r & mask for r in base[:i + 1]]):
            t |= 1 << i
            base[i] ^= 1 << i
    residual = target
    for i, label in enumerate(labels):
        if t >> i & 1:
            residual ^= label
    if not residual:
        return t
    pivots = {}
    for v in labels:
        while v:
            j = v.bit_length() - 1
            if j not in pivots:
                pivots[j] = v
                break
            v ^= pivots[j]
    limit = 2 * len(pivots)
    for k in range(1, min(limit, n) + 1):
        for support in combinations(range(n), k):
            value = 0
            for i in support:
                value ^= labels[i]
            if value != residual:
                continue
            candidate = base.copy()
            toggle = 0
            for i in support:
                toggle |= 1 << i
                candidate[i] ^= 1 << i
            if invertible(candidate):
                return t ^ toggle
    return None


if __name__ == "__main__":
    from random import Random
    rng = Random(42)
    cases = 0
    for n in range(1, 8):
        for trial in range(20):
            rows = [0] * n
            for i in range(n):
                for j in range(i + 1):
                    bit = rng.randrange(2)
                    rows[i] |= bit << j
                    rows[j] |= bit << i
            labels = [rng.randrange(2 if trial % 2 else 8) for _ in rows]
            def syndrome(t):
                out = 0
                for i, label in enumerate(labels):
                    if t >> i & 1:
                        out ^= label
                return out
            fibers = set()
            for t in range(1 << n):
                if invertible([r ^ ((t >> i & 1) << i) for i, r in enumerate(rows)]):
                    fibers.add(syndrome(t))
            for u in range(8):
                t = solve(rows, labels, u)
                assert (t is not None) == (u in fibers)
                if t is not None:
                    assert syndrome(t) == u
                    assert invertible([r ^ ((t >> i & 1) << i) for i, r in enumerate(rows)])
                cases += 1
    print(cases, "syndrome decisions compared with exhaustive completions")
