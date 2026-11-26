"""Exhaustive signed cube-sum compiler check using a tiny independent CNF counter."""
from collections import Counter
from itertools import product
from math import prod
from random import Random


class CNF:
    def __init__(self, n):
        self.n = n
        self.clauses = []

    def fresh(self):
        self.n += 1
        return self.n

    def digit(self, radix):
        # Prefix "some earlier digit was selected" is uniquely determined.
        options = [self.fresh() for _ in range(radix)]
        previous = options[0]
        for choice in options[1:]:
            prefix = self.fresh()
            self.clauses.extend([(-choice, -previous), (-choice, prefix),
                                 (-previous, prefix), (-prefix, previous, choice)])
            previous = prefix
        self.clauses.append((previous,))
        return options

    def factor(self, base, exceptions, radices):
        # Entry zero is the ordinary CNF base. Each other entry is a signed cube.
        sign = self.fresh()
        digits = [self.digit(r) for r in radices]
        assert prod(radices) >= 1 + len(exceptions)
        for i, selected in enumerate(product(*digits)):
            gate = tuple(-s for s in selected)
            if i > len(exceptions):
                self.clauses.append(gate)
            elif i == 0:
                self.clauses.append(gate + (-sign,))
                self.clauses.extend(gate + tuple(clause) for clause in base)
            else:
                polarity, cube = exceptions[i-1]
                self.clauses.append(gate + (sign if polarity < 0 else -sign,))
                self.clauses.extend(gate + (literal,) for literal in cube)
        return sign


def counts(clauses, env, n, signs):
    # Ordinary, unsigned #SAT split by parity of selected negative terms.
    while True:
        pending = []
        for clause in clauses:
            if any(abs(v) in env and env[abs(v)] == (v > 0) for v in clause):
                continue
            remainder = tuple(v for v in clause if abs(v) not in env)
            if not remainder:
                return Counter()
            pending.append(remainder)
        clauses = pending
        unit = next((c[0] for c in clauses if len(c) == 1), None)
        if unit is None:
            break
        env[abs(unit)] = unit > 0
    if not clauses:
        undecided = set(signs) - env.keys()
        total = 1 << (n-len(env))
        if undecided:
            return Counter({0: total//2, 1: total//2})
        return Counter({sum(env[s] for s in signs) % 2: total})
    variable = abs(min(clauses, key=len)[0])
    return sum((counts(clauses, {**env, variable: value}, n, signs)
                for value in (0, 1)), Counter())


def check(n, core, factors):
    formula = CNF(n)
    formula.clauses.extend(core)
    signs = [formula.factor(*f) for f in factors]
    total = 0
    for x in product(range(2), repeat=n):
        env = dict(enumerate(x, 1))
        def lit(v):
            return x[abs(v)-1] == (v > 0)
        expected = Counter({0: int(all(any(map(lit, c)) for c in core))})
        for base, exceptions, _ in factors:
            terms = [0] if all(any(map(lit, c)) for c in base) else []
            terms.extend(int(s < 0) for s, cube in exceptions if all(map(lit, cube)))
            combined = Counter()
            for p, count in expected.items():
                for sign in terms:
                    combined[p ^ sign] += count
            expected = combined
        result = counts(formula.clauses, env, formula.n, signs)
        assert (expected[0], expected[1]) == (result[0], result[1])
        total += result[0] - result[1]
    return total


def main():
    rng = Random(416)
    basis = [((1,),), ((-1, 2),)]
    # Each signed factor has both positive and negative entries; four valid
    # entries in a 2x3 digit grid leave two unused codes.
    specs = [(basis[0], [(1, (-1,)), (-1, (1, 2)), (1, (1, 2))], (2, 3)),
             (basis[1], [(1, (1, -2)), (-1, (-3,))], (2, 2))]
    assert check(3, [(2, 3)], specs) == 4
    cases = 1
    for _ in range(75):
        n = rng.randint(1, 5)
        def clause():
            return tuple(v if rng.randrange(2) else -v
                         for v in rng.sample(range(1, n+1), rng.randint(0, n)))
        factors = []
        for _ in range(rng.randint(1, 3)):
            radices = rng.choice([(1,), (2,), (2, 3), (1, 3, 2), (2, 2, 2)])
            exceptions = [(rng.choice([-1, 1]), clause())
                          for _ in range(rng.randrange(prod(radices)))]
            factors.append(([clause() for _ in range(rng.randrange(3))],
                            exceptions, radices))
        check(n, [clause() for _ in range(rng.randrange(3))], factors)
        cases += 1
    print(f"{cases} signed formula cases passed, both sign bins checked pointwise.")


if __name__ == '__main__':
    main()
