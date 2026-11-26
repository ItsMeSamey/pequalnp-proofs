from itertools import product
from check import graph, witness


def parity(mask, x):
    return (mask & x).bit_count() % 2


def violations(rows, x):
    return sum((parity(row, x) * (x >> i & 1)) << i
               for i, row in enumerate(rows))


def check_diagonal_removal():
    for n in range(1, 4):
        for edges in range(1 << (n*(n-1)//2)):
            adj = graph(n, edges)
            for diagonal in range(1 << n):
                rows = [row ^ (diagonal & (1 << i)) for i, row in enumerate(adj)]
                alternating = [row ^ (diagonal if diagonal >> i & 1 else 0)
                               for i, row in enumerate(rows)]
                assert all(not (row >> i & 1) for i, row in enumerate(alternating))
                for a, b in product(range(1 << n), repeat=2):
                    combinations = [0, a, b, a ^ b]
                    if diagonal not in combinations:
                        continue
                    labels = [(a >> i & 1) | ((b >> i & 1) << 1) for i in range(n)]
                    for target in range(4):
                        expected = {x for x in range(1 << n)
                                    if not violations(rows, x)
                                    and parity(a,x) + 2*parity(b,x) == target}
                        inconsistent = parity(combinations.index(diagonal), target)
                        result = None if inconsistent else witness(alternating, labels, target)
                        assert result in expected if expected else result is None


def check_cut_obstruction():
    rows = [3,21,22,24,14]
    masks = [violations(rows, x) for x in range(32)
             if not parity(13,x) and parity(21,x) and parity(4,x)]
    assert masks == [12,10,17,6]
    assert all(any(not parity(cut,v) for v in masks) for cut in range(32))


if __name__ == '__main__':
    check_diagonal_removal()
    check_cut_obstruction()
    print('Diagonal reductions through dimension three and single-cut obstruction passed.')
