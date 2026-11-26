"""Exhaust all topologically ordered binary monotone circuits on four inputs up to four gates."""

from itertools import combinations, combinations_with_replacement

assignments = [0, 1, 2, 4, 8, 3, 5, 9, 6, 10, 12]
variables = [1, 2, 4, 8]
cross = set(x | y for x in variables[:2] for y in variables[2:])
cross_bits = sum(1 << i for i, mask in enumerate(assignments) if mask in cross)
edge_ids = {mask: 1 << i for i, mask in enumerate(assignments)}
tested = [0] * 5
nonempty = [0] * 5


def enumerate_circuits(wires, depth):
    if depth:
        table, _, pairs = wires[-1]
        if table & ~cross_bits == 0 and table != cross_bits:
            tested[depth] += 1
            nonempty[depth] += bool(table)
            assert pairs.bit_count() <= depth
    if depth == 4:
        return
    for (a, first, p), (b, second, q) in combinations_with_replacement(wires, 2):
        enumerate_circuits(wires + [(a | b, first | second, p | q)], depth + 1)
        merged = 0
        for x in variables:
            for y in variables:
                if x != y and first & x and second & y:
                    merged |= edge_ids[x | y]
        enumerate_circuits(wires + [(a & b, 0, merged)], depth + 1)


inputs = [(sum(1 << i for i, mask in enumerate(assignments) if mask & x), x, 0)
          for x in variables]
enumerate_circuits(inputs, 0)
print("depth, valid circuits, nonempty edge graph")
for d in range(1, 5):
    print(d, tested[d], nonempty[d])
