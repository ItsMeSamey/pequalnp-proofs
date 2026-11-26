from itertools import product
from random import Random
from flat_solver import solve


def valid(x, guards, markers):
    return all((x & m).bit_count() % 2 == rhs for m, rhs in markers) and all(
        not (x >> i & 1) or any(((m & x).bit_count() & 1) ^ c for m, c in lits)
        for i, lits in guards)


rng = Random(10857)
cases = 0
for _ in range(480):
    n = rng.randrange(9)
    guards = [(i, [(rng.getrandbits(i), rng.randrange(2)) for _ in range(rng.randrange(6))])
              for i in range(n)]
    masks = [rng.getrandbits(n) for _ in range(rng.randrange(4))]
    for target in product(range(2), repeat=len(masks)):
        markers = list(zip(masks, target))
        x, l = solve(n, guards, markers)
        reference = any(valid(y, guards, markers) for y in range(1 << n))
        assert reference == (x is not None)
        if x is not None:
            assert valid(x, guards, markers)
        cases += 1

# Dense, unbounded-sharing DAG with two native literals per bit of the prefix.
# Guards with no predecessors are free. Each later bit reads every earlier bit.
for n in (32, 64, 128):
    guards = [(i, [(0, 1)] if i < 8 else [(1 << j, 1) for j in range(i)]) for i in range(n)]
    x, exceptions = solve(n, guards, [((1 << n) - 1, 1)])
    assert x is not None and valid(x, guards, [((1 << n) - 1, 1)])
    assert exceptions == 0
print(cases, 'random marker slices and three dense families passed')

for n in (12, 32, 64):
    guards = [(i, [(1 << (i-1), 0)]) for i in range(1, n)]
    guards[-1][1].append((1, 0))
    markers = [((1 << i) | (1 << (i % 2)), 0) for i in range(2, n)]
    x, exceptions = solve(n, guards, markers)
    assert exceptions == 2 and valid(x, guards, markers)
print("three arbitrarily extensible sparse cycle examples passed")

for n in (24, 48):
    guards = [(1, [(1, 0)])] + [
        (j, [(1, 0), (2, 1), (1 << (j-1), 0)]) for j in range(3, n)
    ]
    x, exceptions = solve(n, guards, [])
    assert exceptions == 1 and valid(x, guards, [])
print("strict-subflat examples passed")
