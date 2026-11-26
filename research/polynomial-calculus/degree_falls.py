"""Exact simultaneous degree-fall closure in the Boolean quotient over F2."""
from itertools import combinations
from pathlib import Path
import json


def bits(v):
    while v:
        b = v & -v
        yield b.bit_length() - 1
        v ^= b


def insert(basis, row):
    while row:
        lead = row.bit_length() - 1
        if lead not in basis:
            basis[lead] = row
            return True
        row ^= basis[lead]
    return False


def compute(specification, cap=3):
    matrix = specification['matrix']
    offset = specification['offset']
    marker = specification['marker']
    n = len(matrix)
    masks = [sum(1 << i for i in s) for degree in range(cap+2)
             for s in combinations(range(n), degree)]
    indices = {mask: j for j, mask in enumerate(masks)}
    cutoff = sum(mask.bit_count() <= cap for mask in masks)
    variable_maps = [[indices[v | (1 << i)] for v in masks[:cutoff]]
                     for i in range(n)]
    basis = {}
    for i, row in enumerate(matrix):
        p = 1 << indices[1 << i] if (offset >> i) & 1 else 0
        for j in bits(row):
            p ^= 1 << indices[(1 << i) | (1 << j)]
        insert(basis, p)
    if marker is not None:
        insert(basis, 1 | sum(1 << indices[1 << i] for i in bits(marker)))
    ranks = [len(basis)]
    # H = span(W and all x_i W) in ambient degree cap+1.
    # A degree-ordered echelon basis of H intersects degree <=cap in its
    # low-pivot rows. All products share one elimination because their top
    # terms are allowed to cancel across distinct multipliers.
    while True:
        old_rank = len(basis)
        high_space = dict(basis)
        for var_map in variable_maps:
            for v in basis.values():
                product = 0
                for j in bits(v):
                    product ^= 1 << var_map[j]
                insert(high_space, product)
        basis = {j: v for j, v in high_space.items() if j < cutoff}
        if len(basis) == old_rank:
            break
        ranks.append(len(basis))
    target = 1 << indices[1 << 10] if marker is None else 1
    found = not insert(dict(basis), target)
    return ranks, found


if __name__ == '__main__':
    for filename in ['affine-base.json', 'unsat-marker.json']:
        spec = json.loads(Path(__file__).with_name(filename).read_text())
        ranks, target = compute(spec)
        print(filename, 'simultaneous ranks', ranks, 'target derived', target)
        if not target:
            raise SystemExit('Unexpected failure to derive target')
