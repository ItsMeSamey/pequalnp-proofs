"""Verify exact expansion by realized accepting cut signatures in tiny shared DAGs."""
from itertools import product
from random import Random


def evaluate(inputs, gates, cut_values=None):
    actual = list(inputs)
    cut_values = cut_values or {}
    for op, left, right in gates:
        a = cut_values.get(left, actual[left])
        b = cut_values.get(right, actual[right])
        actual.append((op >> (2 * a + b)) & 1)
    return actual


def verify(n, gates, cuts):
    rows = []
    signatures = set()
    for x in product((0, 1), repeat=n):
        actual = evaluate(x, gates)
        rows.append((x, actual[-1]))
        if actual[-1]:
            signatures.add(tuple(actual[c] for c in cuts))

    checks = 0
    for x, expected in rows:
        total = 0
        for signature in signatures:
            pins = dict(zip(cuts, signature))
            gated = evaluate(x, gates, pins)
            total += gated[-1] * all(gated[c] == bit for c, bit in pins.items())
            checks += 1
        assert total == expected
    return len(rows), checks


rng = Random(8712)
rows = tests = 0
for case in range(300):
    n = rng.randint(2, 6)
    gates = []
    for gate in range(rng.randint(3, 18)):
        high = n + gate
        gates.append((rng.randrange(16), rng.randrange(high), rng.randrange(high)))
    cuts = sorted(rng.sample(range(n, n + len(gates) - 1),
                             rng.randrange(min(5, len(gates) - 1) + 1)))
    r, t = verify(n, gates, cuts)
    rows += r
    tests += t
print(f"300 DAGs, {rows} truth-table rows, {tests} accepting-signature branch tests")
