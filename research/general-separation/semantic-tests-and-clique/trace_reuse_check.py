"""Check GF(2) residual ranks and one-way row counts on exact native cycles."""
from math import comb, factorial
from onehot_hc_rank_check import cycle_rows

for n in range(2, 9):
    for k in range(1, n):
        rows = [frozenset(row) for row in cycle_rows(n, k)]
        pivots = {}
        for row in rows:
            while row:
                pivot = min(row)
                if pivot not in pivots:
                    pivots[pivot] = row
                    break
                row = row.symmetric_difference(pivots[pivot])
        sizes = range(1, min(k, n-k)+1)
        rank = sum(comb(k,m)*comb(n-k,m)*(1 << (m-1)) for m in sizes)
        classes = sum(comb(k,m)*comb(n-k,m)*factorial(m) for m in sizes)
        assert len(pivots) == rank
        assert len(set(rows)) == classes
    print(f"n={n}, passed {n-1} cuts")
