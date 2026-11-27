"""Bounded differential checks for automatic quaternary central decomposition."""

from itertools import combinations_with_replacement
from random import Random

from auto_central import find_split, find_tree
from central_uplift import expand_witness, reduce_central
from check_central_uplift import attainable, subsets, three_name


def oracle_splits(columns):
    # Enumerate the actual K-linear spans as paired binary coordinate masks.
    n = len(columns)
    assert 2 <= n <= 8 and all(0 <= v < 16 for col in columns for v in col)
    spans = [set() for _ in range(1 << n)]
    spans[0] = {(0, 0)}
    for mask in range(1, 1 << n):
        bit = mask & -mask
        x, y = columns[bit.bit_length() - 1]
        multiples = [(0, 0), (x, y), (y, x ^ y), (x ^ y, x)]
        spans[mask] = {(a ^ c, b ^ d) for a, b in spans[mask ^ bit]
                       for c, d in multiples}
    all_ids = (1 << n) - 1
    allowed = set()
    for mask in range(1, all_ids):
        overlap = len(spans[mask] & spans[all_ids ^ mask])
        if overlap == 1:
            return None  # disconnected
        if overlap == 4 and 2 <= mask.bit_count() <= n - 2:
            allowed.add(mask)
    return allowed


def check_split(columns):
    allowed = oracle_splits(columns)
    if allowed is None:
        return False
    split = find_split(columns)
    if split is None:
        assert not allowed, (columns, allowed)
    else:
        ids = list(split)
        assert len(set(ids)) == len(ids) and all(i in range(len(columns)) for i in ids)
        assert sum(1 << i for i in ids) in allowed, (columns, ids, allowed)
    return True


def check_tree(private, height):
    tree = find_tree(private, height)
    for tags in ([0] * len(private), [i % 4 for i in range(len(private))]):
        cols, expr = reduce_central(private, height, tags, tree, three_name)
        physical_named = [h | t << 2 for h, t in zip(height, tags)]
        physical = any(attainable(private, physical_named, ids) == set(range(4))
                       for ids in subsets(len(private)))
        pc = [p for p, _, _ in cols]
        nc = [h | t << 2 for _, h, t in cols]
        central = False
        for ids in subsets(len(cols)):
            if attainable(pc, nc, ids) == set(range(4)):
                central = True
                full = expand_witness(cols, expr, ids, private, height, tags)
                assert attainable(private, physical_named, full) == set(range(4))
        assert central == physical


def main():
    # Five distinct projective points in dimension two, including nonbinary ones.
    points = [(1, 0), (2, 0), (3, 0), (1, 2), (3, 2)]
    count = 0
    for n in (4, 5):
        for cols in combinations_with_replacement(points, n):
            count += check_split(list(cols))

    for cols in [
        [(1, 0), (2, 0), (4, 0), (7, 0)],  # four-element circuit
        [(1, 0), (2, 0), (3, 0), (4, 0), (7, 0)],  # triangles in series
        [(1, 0), (0, 1), (1, 1), (1, 0)],  # scalar multiples
    ]:
        assert check_split(cols)
        count += 1
    rng = Random(4286)
    for _ in range(48):
        cols = [(rng.randrange(8), rng.randrange(8)) for _ in range(6)]
        count += check_split(cols)

    for p, h in [
        ([1, 1, 1], [0, 1, 2]),
        ([1, 3, 1, 2, 1], [0, 3, 1, 1, 2]),
        ([1, 2, 3, 1, 2, 3], [0, 0, 0, 1, 2, 3]),
        ([1, 1, 1, 1, 1, 1], [0, 1, 2, 0, 1, 2]),
        ([1, 1, 2, 7, 4, 1], [0, 1, 1, 0, 3, 2]),
    ]:
        check_tree(p, h)
    random_trees = 0
    for _ in range(36):
        p = [rng.randrange(1, 8) for _ in range(6)]
        h = [rng.randrange(4) for _ in range(6)]
        if oracle_splits([(v, 0) for v in p]) is None:
            continue
        if attainable(p, h, range(len(p))) == set(range(4)):
            check_tree(p, h)
            random_trees += 1
    assert random_trees > 0
    for p, h in [
        ([1, 1, 1], [0, 0, 0]),
        ([1, 1, 1], [0, 1, 0]),
        ([1, 1, 2, 2], [0, 1, 0, 2]),
    ]:
        try:
            find_tree(p, h)
        except ValueError:
            continue
        raise AssertionError((p, h))
    print(f"checked {count} connected splits, {5 + random_trees} central trees and three rejections")


if __name__ == "__main__":
    main()
