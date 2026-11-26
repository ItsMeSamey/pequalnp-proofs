from itertools import product
from random import Random
from deficiency_one import solve_deficiency_one
from hall_sat import matching


def check(rows, n):
    def sat(a):
        return all(any(a[abs(lit)] == (lit > 0) for lit in row) for row in rows)
    expected = any(sat(dict(enumerate(bits, 1))) for bits in product((False, True), repeat=n))
    deficient = len(rows) - len(matching([{abs(lit) for lit in row} for row in rows])[0]) > 1
    try:
        model = solve_deficiency_one(rows)
    except ValueError:
        assert deficient
        return
    assert not deficient and (model is not None) == expected
    assert model is None or sat(model)


def clauses(n):
    return [tuple((i + 1) * s for i, s in enumerate(signs) if s)
            for signs in product((-1, 0, 1), repeat=n)]


if __name__ == '__main__':
    pool = clauses(2)
    for mask in range(1 << len(pool)):
        check([r for i, r in enumerate(pool) if mask & (1 << i)], 2)
    rng = Random(4051)
    pool = clauses(5)
    for _ in range(5000):
        check(rng.sample(pool, rng.randrange(11)), 5)
    for depth in range(2, 8):
        rows = [()]
        for level in range(depth):
            rows = [r + (s * ((1 << level) + i),)
                    for i, r in enumerate(rows) for s in (1, -1)]
        assert solve_deficiency_one(rows) is None
        assert solve_deficiency_one(rows[1:]) is not None
    assert solve_deficiency_one([[1], [1], [2, -2]]) == {1: True, 2: False}
    print('512 exhaustive, 5000 random, depths 2–7, and normalization checks passed')
