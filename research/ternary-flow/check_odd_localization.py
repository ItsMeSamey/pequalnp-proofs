"""Enumerate native truth tables and verify target-local pruning over F3."""
from itertools import product
from random import Random

def check(rows, coeff):
    n = len(rows)
    traces = []
    for i, row in enumerate(rows):
        traces.append([coeff[i] * (x >> i & 1) * ((row & x).bit_count() % 2)
                       for x in range(1 << n)])
    vals = [sum(column) % 3 for column in zip(*traces)]
    target = sum(1 << i for i in range(n) if any(
        vals[x] != vals[x ^ (1 << i)] for x in range(1 << n)))
    keep = target
    for i, row in enumerate(rows):
        if (target >> i) & 1:
            keep |= row
    assert all(vals[x] == sum(traces[i][x] for i in range(n)
                              if keep >> i & 1) % 3 for x in range(1 << n))

def main():
    total = 0
    for rows in product(range(8), repeat=3):
        for coeff in product(range(3), repeat=3):
            check(rows, coeff)
            total += 1
    rng = Random(421)
    for _ in range(5000):
        n = rng.randrange(4, 8)
        check([rng.randrange(1 << n) for _ in range(n)],
              [rng.randrange(3) for _ in range(n)])
        total += 1
    print(f'{total} exact localizations passed')

if __name__ == '__main__':
    main()
