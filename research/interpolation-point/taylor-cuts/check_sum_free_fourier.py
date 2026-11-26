from fractions import Fraction
from math import prod
from random import Random

rng = Random(876)
accepted = 0
for trial in range(500):
    n = rng.randint(2, 5)
    formula = [
        [(v, rng.randrange(2)) for v in rng.sample(range(n), rng.randint(2, min(3, n)))]
        for _ in range(rng.randint(1, 4))
    ]
    edges = [(var, sign, c) for c, clause in enumerate(formula) for var, sign in clause]
    negative = set()
    total = 0
    for vector in range(1 << len(edges)):
        selected = [edge for i, edge in enumerate(edges) if vector >> i & 1]
        if any(sum(v == u for v, s, c in selected) % 2 for u in range(n)):
            continue
        touched = {c for v, s, c in selected}
        parity = (len(touched) + sum(1 - sign for v, sign, c in selected)) % 2
        magnitude = prod((1 << len(clause)) - 1 for c, clause in enumerate(formula) if c not in touched)
        total += (-1 if parity else 1) * magnitude
        if parity:
            negative.add(vector)
    count = sum(all(any((a >> v & 1) != s for v, s in clause) for clause in formula)
                for a in range(1 << n))
    assert Fraction(total, 1 << len(edges)) == Fraction(count, 1 << n)
    if not any(x ^ y in negative for x in negative for y in negative):
        lower = prod(1 - Fraction(2, 1 << len(c)) for c in formula)
        assert Fraction(count, 1 << n) >= lower
        accepted += 1
print(f'500 Fourier equalities; {accepted} certificates checked')
