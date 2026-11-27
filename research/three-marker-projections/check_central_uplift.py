"""Small, bounded differential checks for the supplied central-port reduction."""

from itertools import product

from central_uplift import expand_witness, reduce_central


def attainable(private, named, ids):
    sums = {(0, 0)}
    for i in ids:
        sums |= {(p ^ private[i], n ^ named[i]) for p, n in sums}
    return {n for p, n in sums if p == 0}


def subsets(n):
    assert n <= 10, "exhaustive oracle is for small tests only"
    for mask in reversed(range(1 << n)):
        yield [i for i in range(n) if mask >> i & 1]


def three_name(private, named, target):
    return next((ids for ids in subsets(len(private))
                 if attainable(private, named, ids) == {0, target}), None)


def check(private, height, tag, tree, branches):
    columns, expressions = reduce_central(private, height, tag, tree, three_name)
    assert len(columns) == len(expressions)
    named = [h | t << 2 for h, t in zip(height, tag)]
    expected = set()
    for branch in branches:
        for local in subsets(len(branch)):
            ids = [branch[j] for j in local]
            p = h = t = 0
            for i in ids:
                p ^= private[i]
                h ^= height[i]
                t ^= tag[i]
            if p == 1 and independent(private, ids):
                expected.add((tuple(branch), h, t))

    actual = set()
    for (_, h, t), ids in zip(columns, expressions):
        branch, = (b for b in branches if ids and set(ids) <= set(b))
        assert independent(private, ids)
        p = n = 0
        for i in ids:
            p ^= private[i]
            n ^= named[i]
        assert p == 1 and n == h | t << 2
        actual.add((tuple(branch), h, t))
    assert actual == expected and len(columns) == len(actual)
    central_p = [p for p, _, _ in columns]
    central_n = [h | t << 2 for _, h, t in columns]
    assert len(set(central_p)) == 1 and central_p[0] != 0
    goal = set(range(4))
    yes = False
    for ids in subsets(len(columns)):
        if attainable(central_p, central_n, ids) == goal:
            yes = True
            full = [i for j in ids for i in expressions[j]]
            assert len(set(full)) == len(full)
            assert expand_witness(columns, expressions, ids, private, height, tag) == sorted(full)
            assert attainable(private, named, full) == goal
    assert yes == any(attainable(private, named, ids) == goal
                      for ids in subsets(len(private)))
    return yes


def independent(private, ids):
    sums = {0}
    for i in ids:
        if private[i] in sums:
            return False
        sums |= {p ^ private[i] for p in sums}
    return True


def main():
    private = [1, 3, 1, 2, 1]
    height = [0, 3, 1, 1, 2]
    tree = [0, 2, [[3, 1], 4]]
    branches = [[0], [2], [3, 1, 4]]
    for a, b, c in product(range(4), repeat=3):
        tag = [a, b, a, 0, c]
        assert check(private, height, tag, tree, branches) == (a in (b, c))
    assert not check(private, height, [0, 0, 1, 0, 0], tree, branches)
    # A rank-two private boundary tests central relations beyond even parity.
    p2 = [1, 2, 3, 1, 2, 3]
    h2 = [0, 0, 0, 1, 2, 3]
    singleton_tree = [4, 1, 5, 2, 0, 3]
    for t2 in ([0] * 6, [0, 1, 2, 3, 0, 1]):
        cols, expr = reduce_central(p2, h2, t2, singleton_tree, three_name)
        assert sorted(tuple(ids) for ids in expr) == [(i,) for i in range(6)]
        pc = [p for p, _, _ in cols]
        nc = [h | t << 2 for _, h, t in cols]
        n2 = [h | t << 2 for h, t in zip(h2, t2)]
        for ids in subsets(6):
            physical = [expr[j][0] for j in ids]
            assert attainable(pc, nc, ids) == attainable(p2, n2, physical)
    for p, h, tr in [
        (private, height, [0, 2, [[3, 1], 3]]),
        (private, height, [0, 2, [3, 1]]),
        ([1, 2, 4], [0, 1, 2], [0, 1, 2]),
        ([1, 1, 1, 1], [0, 1, 2, 2], [0, 1, 2, 3]),
        ([1, 2, 1, 2], [0, 0, 1, 2], [[0, 1], [2, 3]]),
        (private, [0, 3, 1, 0, 2], tree),
    ]:
        try:
            reduce_central(p, h, [0] * len(p), tr, three_name)
        except ValueError:
            continue
        raise AssertionError((p, h, tr))
    print("central uplift differential checks passed")


if __name__ == "__main__":
    main()
