from itertools import combinations, product
from random import Random
from project import component_tables, label, pair_queries


def check(rows, columns):
    true = {label(columns,x) for x in range(1 << len(rows))
            if all(not(x >> i & 1 and (x & row).bit_count() % 2)
                   for i,row in enumerate(rows))}
    for extract in (pair_queries, component_tables):
        found, absent = extract(rows,columns)
        assert not (found.keys() & absent)
        assert len(found) + len(absent) >= 7
        assert not (true & absent)
        for c,x in found.items():
            assert label(columns,x) == c
            assert all(not(x >> i & 1 and (x & row).bit_count() % 2)
                       for i,row in enumerate(rows))
        if absent:
            assert found.keys() == true


if __name__ == '__main__':
    for n in range(4):
        pairs = list(combinations(range(n),2))
        for code in range(1 << len(pairs)):
            rows = [0]*n
            for k,(i,j) in enumerate(pairs):
                if code >> k & 1:
                    rows[i] |= 1 << j
                    rows[j] |= 1 << i
            for columns in product(range(8),repeat=n):
                check(rows,columns)
    rng = Random(6728)
    for rep in range(500):
        n = rng.randrange(4,11)
        rows = [0]*n
        for i,j in combinations(range(n),2):
            if (rep % 2 or (i < n//2) == (j < n//2)) and rng.randrange(2):
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        check(rows, [rng.randrange(8) for _ in rows])
    check([10,5,2,1], [1,1,2,4])
    print("Three-bit projection certificates verified exhaustively for n≤3 and on 500 seeded cases.")
