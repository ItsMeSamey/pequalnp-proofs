from itertools import combinations, product
from random import Random
from hall_sat import solve


def satisfies(rows, model):
    return all(any(model[abs(x)] == (x > 0) for x in row) for row in rows)


def verify(rows):
    variables = sorted({abs(v) for row in rows for v in row})
    expected = any(satisfies(rows, dict(zip(variables, bits)))
                   for bits in product((False, True), repeat=len(variables)))
    auto = solve(rows)
    for result in [auto, solve(rows, auto["core"]), solve(rows, variables)]:
        model = result["model"]
        assert (model is not None) == expected and (model is None or satisfies(rows, model))


clauses = [tuple(s * i for i, s in enumerate(signs, 1) if s)
           for signs in product((-1, 0, 1), repeat=2)]
for size in range(len(clauses) + 1):
    for rows in combinations(clauses, size):
        verify(rows)
rng = Random(512)
for _ in range(1000):
    verify([[rng.choice((-3, -2, -1, 1, 2, 3)) for _ in range(rng.randrange(6))]
            for _ in range(rng.randrange(12))])
verify([[1, -1], [2, 2], []])
try:
    solve([[1], [-1]], [])
except ValueError:
    pass
else:
    raise AssertionError("accepted invalid supplied core")
for n in range(1, 12):
    rows = [[1], [-n]] + [[-i, i + 1] for i in range(1, n)]
    r = solve(rows)
    assert r["model"] is None and r["assignments_tested"] == 2**n
print("Passed 512 exhaustive formulas, 1000 random formulas, edge cases, and 11 exponential examples.")
for depth in range(2, 5):
    leaves = [[]]
    node = 1
    for _ in range(depth):
        children = []
        for path in leaves:
            children.extend([path + [node], path + [-node]])
            node += 1
        leaves = children
    r = solve(leaves)
    assert r["model"] is None and r["assignments_tested"] == 2**(node-1)
print("Passed three unit-free, pure-free deficiency-one tree formulas.")
