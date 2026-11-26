from itertools import combinations, product
from math import comb
from random import Random

rng = Random(26)
cases = 0
for n in range(1, 9):
    universe = list(product((0, 1), repeat=n))
    for _ in range(25):
        k = rng.randrange(1, min(n, 3) + 1)
        clauses = []
        for _ in range(rng.randrange(1, 6)):
            variables = rng.sample(range(n), rng.randrange(1, k + 1))
            values = [rng.randrange(2) for _ in variables]
            clauses.append((dict(zip(variables, values)), rng.randrange(-3, 4)))

        def score(x):
            return sum(weight for literals, weight in clauses
                       if all(x[index] == value for index, value in literals.items()))

        scores = {x: score(x) for x in universe}
        levels = set(scores.values())
        for bound in range(1, len(levels) + 2):
            discovered = {s for x, s in scores.items() if sum(x) <= k * bound}
            assert (len(discovered) <= bound) == (len(levels) <= bound)
            if len(discovered) <= bound:
                assert discovered == levels
        d = min(n, k * (len(levels) - 1))
        coeff = [sum((-1)**j * comb(n-t, j) * 2**(n-t-j)
                     for j in range(d-t+1)) for t in range(d+1)]
        for target in levels | {99}:
            count = sum(coeff[sum(x)] for x, s in scores.items()
                        if sum(x) <= d and s == target)
            assert count == sum(s == target for s in scores.values())
        cases += 1
print(f"{cases} signed score systems")
