from itertools import combinations, product


def powerset(seq):
    seq = tuple(seq)
    for size in range(len(seq) + 1):
        yield from map(frozenset, combinations(seq, size))


def bad_edges(rows, blocks):
    return {frozenset(i for i, (a, b) in enumerate(zip(x, y)) if a != b)
            for x in rows for y in rows
            if any(tuple(y[i] if i in block else x[i] for i in range(len(x)))
                   not in rows for block in blocks)}


def product_fibers(rows, blocks, anchor):
    fibers = {}
    for row in rows:
        key = tuple(row[i] for i in sorted(anchor))
        fibers.setdefault(key, []).append(row)
    for fiber in fibers.values():
        cardinality = 1
        for block in blocks:
            cardinality *= len({tuple(row[i] for i in block if i not in anchor)
                                for row in fiber})
        if cardinality != len(fiber):
            return False
    return True


def check():
    trials = 0
    for alph, n in [(2, 3), (3, 2)]:
        universe = tuple(product(range(alph), repeat=n))
        for rows in powerset(universe):
            for blocks in [[{i} for i in range(n)], [{0}, set(range(1, n))]]:
                edges = bad_edges(rows, blocks)
                for anchor in powerset(range(n)):
                    assert product_fibers(rows, blocks, anchor) == all(anchor & e for e in edges)
                    trials += 1
    u = 3
    for family in powerset(e for e in powerset(range(u)) if e):
        if not family:
            continue
        left = set(range(u))
        right = set(range(u, 2*u+1))
        rows = {(0,)*(2*u+1)}
        for e in family:
            for j in right:
                rows.add(tuple(int(i in e or i == j) for i in range(2*u+1)))
        assert bad_edges(rows, [left, right]) == {e | {j} for e in family for j in right}
        trials += 1
    print(f'{trials} fiber and reduction checks passed')


if __name__ == '__main__':
    check()
