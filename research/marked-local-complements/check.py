"""Affine state transport for local complementation of marked simple graphs."""
from itertools import combinations, permutations, product
from random import Random


def lc(rows, v):
    neighborhood = rows[v]
    return tuple(row ^ (neighborhood ^ (1 << i)) if neighborhood >> i & 1 else row
                 for i, row in enumerate(rows))


def step(rows, columns, target, v):
    updated = tuple(label ^ columns[v] if rows[v] >> i & 1 else label
                    for i, label in enumerate(columns))
    return lc(rows, v), updated, target ^ columns[v]


def transport(rows, x, v):
    return x ^ ((1 ^ ((rows[v] & x).bit_count() & 1)) << v)


def defects(rows, x):
    return sum((x >> i & 1) * ((row & x).bit_count() & 1) << i
               for i, row in enumerate(rows))


def label(columns, x):
    result = 0
    for i, column in enumerate(columns):
        if x >> i & 1:
            result ^= column
    return result


def augment(rows, columns, target, t):
    n = len(rows)
    full = list(rows) + [0] * (2*t)
    for j in range(t):
        p = n + 2*j
        for i, column in enumerate(columns):
            if column >> j & 1:
                full[i] |= 3 << p
                full[p] |= 1 << i
                full[p+1] |= 1 << i
        if target >> j & 1:
            full[p] |= 1 << (p+1)
            full[p+1] |= 1 << p
    return tuple(full)


def decode(full, n, t):
    rows = tuple(row & ((1 << n)-1) for row in full[:n])
    columns = [0] * n
    target = 0
    for j in range(t):
        p = n + 2*j
        for i in range(n):
            assert (full[i] >> p & 1) == (full[i] >> (p+1) & 1)
            columns[i] |= (full[i] >> p & 1) << j
        target |= (full[p] >> (p+1) & 1) << j
    return rows, tuple(columns), target


def normalize(rows, columns, target, x):
    history = []
    initial = defects(rows, x)
    for i in range(len(rows)):
        if x >> i & 1 and not initial >> i & 1:
            x = transport(rows, x, i)
            rows, columns, target = step(rows, columns, target, i)
            history.append(i)
    assert x == initial and defects(rows, x) == initial
    return rows, columns, target, x, history


def sparse_solution(columns, target):
    pivots = {}
    for i, column in enumerate(columns):
        mask = 1 << i
        while column:
            k = column.bit_length()-1
            if k not in pivots:
                pivots[k] = column, mask
                break
            row, source = pivots[k]
            column ^= row
            mask ^= source
    x = 0
    while target:
        k = target.bit_length()-1
        if k not in pivots:
            return None
        row, source = pivots[k]
        target ^= row
        x ^= source
    return x


def graphs(n):
    pairs = list(combinations(range(n), 2))
    for code in range(1 << len(pairs)):
        rows = [0] * n
        for k, (i, j) in enumerate(pairs):
            if code >> k & 1:
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        yield tuple(rows)


def exhaustive():
    count = 0
    for n in range(4):
        for rows in graphs(n):
            for columns in product(range(4), repeat=n):
                target = 0
                full = augment(rows, columns, target, 2)
                reachable = set()
                for length in range(n+1):
                    for seq in permutations(range(n), length):
                        moved = full
                        for i in seq:
                            moved = lc(moved, i)
                        reachable.add(decode(moved, n, 2)[2])
                actual = set()
                for x in range(1 << n):
                    defect = defects(rows, x)
                    signature = label(columns, x)
                    if not defect:
                        actual.add(signature)
                    for i in range(n):
                        new = step(rows, columns, target, i)
                        assert decode(lc(full, i), n, 2) == new
                        y = transport(rows, x, i)
                        assert defects(new[0], y) == defect
                        assert label(new[1], y) ^ new[2] == signature
                        assert transport(new[0], y, i) == x
                assert actual == reachable
                count += 1
    return count


def random_tests():
    rng = Random(27102)
    for _ in range(1000):
        n = rng.randrange(1, 14)
        rows = [0]*n
        for i,j in combinations(range(n), 2):
            if rng.randrange(2):
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        rows = tuple(rows)
        columns = tuple(rng.randrange(8) for _ in range(n))
        target = rng.randrange(8)
        x = sparse_solution(columns, target)
        if x is None:
            assert all(label(columns, s) != target for s in range(1 << n))
            continue
        assert label(columns,x) == target and x.bit_count() <= 3
        new, labels, z, candidate, history = normalize(rows, columns, target, x)
        assert label(labels,candidate) == z and candidate.bit_count() in (0,2)
        if candidate:
            u,v = (i for i in range(n) if candidate >> i & 1)
            assert new[u] >> v & 1 and z == labels[u] ^ labels[v]
            assert len(history) <= 1
        full = augment(rows, columns, target, 3)
        for i in history:
            full = lc(full,i)
        assert decode(full,n,3) == (new,labels,z)


if __name__ == '__main__':
    count = exhaustive()
    random_tests()
    print(f'{count} exhaustive two-marker graphs/labelings and 1000 three-marker cases passed.')
