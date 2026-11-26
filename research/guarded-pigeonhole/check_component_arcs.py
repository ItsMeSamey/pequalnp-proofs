"""Exhaust all single-arc choices on three marked reciprocal pairs."""
from itertools import combinations, product

def main():
    pairs = list(combinations(range(3), 2))
    checked = 0
    for arcs in product(range(9), repeat=3):
        rows = [(1 << i) | (1 << (i ^ 1)) for i in range(6)]
        outgoing = set()
        for (left, right), mode in zip(pairs, arcs):
            if mode == 0:
                continue
            source, target = (left, right) if mode <= 4 else (right, left)
            ends = (mode - 1) % 4
            rows[2*source + ends//2] |= 1 << (2*target + ends%2)
            outgoing.add(source)
        solutions = [x for x in range(64)
                     if all(not (x >> i & 1) or not ((x & row).bit_count() % 2)
                            for i, row in enumerate(rows))]
        for marker in range(64):
            actual = all(not ((marker & x).bit_count() % 2) for x in solutions)
            expected = all(((marker >> (2*c)) & 3) in ((0,) if c in outgoing else (0,3))
                           for c in range(3))
            assert actual == expected
            checked += 1
    print(f'{checked} graph-marker pairs passed')

if __name__ == '__main__':
    main()
