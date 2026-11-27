"""Exact GF(16) checker, modulus X^4+X+1. Pin and dummy indexes are zero-based."""
from functools import reduce
from itertools import permutations
from operator import xor


def multiply(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 16:
            a ^= 19
        b >>= 1
    return result


PRODUCT = [[multiply(a,b) for b in range(16)] for a in range(16)]
RECIP = [0] + [row.index(1) for row in PRODUCT[1:]]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def inverse(matrix):
    n = len(matrix)
    rows = [row[:] + unit for row, unit in zip(matrix, identity(n))]
    for j in range(n):
        p = next((i for i in range(j,n) if rows[i][j]), None)
        if p is None:
            return None
        rows[j], rows[p] = rows[p], rows[j]
        scale = PRODUCT[RECIP[rows[j][j]]]
        rows[j] = [scale[v] for v in rows[j]]
        for i in range(n):
            if i != j and rows[i][j]:
                factor = PRODUCT[rows[i][j]]
                rows[i] = [a ^ factor[b] for a,b in zip(rows[i],rows[j])]
    return [row[n:] for row in rows]


def pivot(matrix, mask):
    # Swap indicated input/output pairs, then chart the resulting relation.
    units = identity(len(matrix))
    inputs = [row if mask >> i & 1 else units[i] for i,row in enumerate(matrix)]
    outputs = [units[i] if mask >> i & 1 else row for i,row in enumerate(matrix)]
    back = inverse(inputs)
    if back is None:
        return None
    return [[reduce(xor, (PRODUCT[a][b] for a,b in zip(row,col)), 0)
             for col in zip(*back)] for row in outputs]


def components(rows, live):
    while live:
        seen = live & -live
        todo = seen
        while todo:
            head = todo & -todo
            todo ^= head
            new = rows[head.bit_length()-1] & live & ~seen
            todo |= new
            seen |= new
        yield [i for i in range(len(rows)) if seen >> i & 1]
        live &= ~seen


def gauge(matrix, group, seed):
    scales = {group[0]: seed}
    queue = [group[0]]
    for i in queue:
        for j in group:
            coeff = matrix[i][j]
            if coeff:
                required = RECIP[PRODUCT[scales[i]][coeff]]
                if j in scales and scales[j] != required:
                    return False
                if j not in scales:
                    scales[j] = required
                    queue.append(j)
    assert len(scales) == len(group)
    return True


def eligible(matrix):
    n = len(matrix)-1  # Last column is the dummy drift.
    rows = [sum(bool(c) << j for j,c in enumerate(row[:n])) for row in matrix[:n]]
    for group in components(rows, (1 << n)-1):
        binary = any(gauge(matrix, group, seed) for seed in range(1,16))
        proportional = any(all(PRODUCT[matrix[i][-1]][matrix[i][-1]] ==
                               PRODUCT[t][matrix[i][i]] for i in group) for t in range(16))
        if not binary and not proportional:
            return False
    return True


def examine(A, order):
    n = len(A)
    full = (1 << n)-1
    assert all(not (row >> i & 1) and all((row >> j & 1) == (A[j] >> i & 1)
               for j in range(n)) for i,row in enumerate(A))
    connectivity = min(mask.bit_count() for mask in range(1 << n)
                       if len(list(components(A, full ^ mask))) > 1)
    cutsums = {reduce(xor, (A[i] & ~7 for i in range(3) if s >> i & 1), 0) for s in range(8)}
    assert len(cutsums) == 8
    witnesses = [x for x in range(7,full+1,8)
                 if all(not ((row & x).bit_count() & 1) for i,row in enumerate(A) if x >> i & 1)]
    bases = charts = with_dummy = passing = 0
    a,b,c = order
    for d in range(1 << n):
        matrix = [[((A[i] ^ (d & (1 << i))) >> j) & 1 for j in range(n)] for i in range(n)]
        base = inverse(matrix)
        if base is None:
            continue
        bases += 1
        cap = [row + [0] for row in base] + [[0]*(n+1)]
        for i in range(n):
            cap[i][i] ^= 1
        for i,j,t in ((b,c,2),(a,c,4),(a,b,8),(a,n,1),(b,n,2),(c,n,4)):
            cap[i][j] ^= t
            cap[j][i] ^= t
        # Exactly all pin-containing subsets, including the empty free subset.
        for mask in range(7, 1 << (n+1), 8):
            chart = pivot(cap, mask)
            if chart is not None:
                charts += 1
                with_dummy += (mask >> n) & 1
                passing += eligible([row[3:] for row in chart[3:]])
    return min(row.bit_count() for row in A), connectivity, witnesses, bases, charts, with_dummy, passing


if __name__ == "__main__":
    cases = (([106,21,90,85,110,81,61], [15,71], 65,1820),
             ([116,56,41,86,75,71,57], [],67,1876))
    for rows, witnesses, bases, charts in cases:
        for order in permutations(range(3)):
            result = examine(rows, order)
            assert result[1:5] == (3, witnesses, bases, charts)
            assert result[-1] == 0
            print(order, result)
