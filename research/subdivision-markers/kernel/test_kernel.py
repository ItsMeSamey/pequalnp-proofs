from itertools import combinations_with_replacement, product
from random import Random
from kernel import Basis, certificate, cover, kernelize, solve


def value(pairs, word):
    s = 0
    for pair, x in zip(pairs, word, strict=True):
        s ^= (0, *pair)[x]
    return s


def check(pairs, targets):
    selected, groups = certificate(pairs)
    assert len({e // 2 for e in selected}) == len(selected)
    basis = Basis()
    for e in selected:
        assert basis.add(pairs[e // 2][e % 2])
    basis = Basis()
    for i in groups:
        for x in pairs[i]:
            basis.add(x)
    assert len(selected) == len(basis.rows) + len(pairs) - len(groups)
    possible = {value(pairs, w) for w in product(range(3), repeat=len(pairs))}
    for h in targets:
        result = kernelize(pairs, h)
        if result:
            p, t, k, lift = result
            assert not p or len(p) < k
            for w in product(range(3), repeat=len(p)):
                if value(p, w) == t:
                    assert value(pairs, lift(w)) == h
        w = solve(pairs, h, 2)
        assert (w is not None) == (h in possible)
        if w is not None:
            assert value(pairs, w) == h


if __name__ == '__main__':
    for b in range(5):
        boxes = cover(b)
        for w in product(range(3), repeat=b):
            assert any(all(a != x for a, x in zip(box, w)) for box in boxes)
    n = 0
    for m in range(5):
        for pairs in combinations_with_replacement(list(combinations_with_replacement(range(4), 2)), m):
            check(pairs, range(5))
            n += 1
    rng = Random(72931)
    for _ in range(500):
        m, k = rng.randrange(8), rng.randrange(1, 11)
        pairs = [tuple(rng.randrange(1 << k) for _ in range(2)) for _ in range(m)]
        check(pairs, [rng.randrange(1 << k), value(pairs, [rng.randrange(3) for _ in pairs])])
        n += 1
    print(n, 'instances passed')
