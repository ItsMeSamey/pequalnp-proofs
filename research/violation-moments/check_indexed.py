"""Check reconstruction with an oracle that rejects over-order queries."""
from itertools import combinations
from random import Random
from indexed import joint_exponent


def direct(clauses, selected):
    literals = set().union(*(clauses[i] for i in selected))
    if any(-x in literals for x in literals):
        return None
    return len(literals)


def run(clauses, width, target):
    def limited(indices):
        assert len(indices) <= width.bit_length() + 1
        return direct(clauses, indices)
    expected = direct(clauses, target)
    got = joint_exponent(target, width, limited)
    assert got == expected, (clauses, target, expected, got)


def parity_scopes(m, parity):
    variables = [s for s in range(1 << m) if s.bit_count() % 2 == parity]
    return [{j for j, mask in enumerate(variables, 1) if mask & (1 << i)}
            for i in range(m)]


if __name__ == "__main__":
    rng = Random(173272)
    for _ in range(220):
        width = rng.randrange(1, 13)
        n = rng.randrange(1, 17)
        cls = [set(rng.sample(range(1, n + 1), rng.randrange(min(width, n) + 1)))
               for _ in range(rng.randrange(1, 13))]
        target = rng.sample(range(len(cls)), rng.randrange(len(cls) + 1))
        run(cls, width, target)
        signed = [{x if rng.getrandbits(1) else -x for x in c} for c in cls]
        run(signed, width, target)
    run([{1,-1}, set()], 2, [1,0])
    for m in range(2, 8):
        a, b = (parity_scopes(m, p) for p in range(2))
        for j in range(m):
            for ids in combinations(range(m), j):
                assert direct(a, ids) == direct(b, ids)
        ids = list(range(m))
        assert direct(a, ids) + 1 == direct(b, ids)
        for clauses in (a, b):
            run(clauses, 1 << (m-2), ids)
    print("Passed 440 seeded targets, tautology, and parity trades m=2..7.")
