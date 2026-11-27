"""Verify portfolio decisions and witnesses on signed, original-variable clauses."""
from itertools import product
from random import Random
from original_cnf import accepts_cnf, compile_cnf
from portfolio import solve


def main():
    rng = Random(90021)
    cube = tuple(tuple(i * j for i, j in zip((1, 2, 3), signs))
                 for signs in product((-1, 1), repeat=3))
    formulas = [(0, ()), (0, ((),)), (6, ((1, 1, 2), (-2, 3), (-3, 1), (5, -5))),
                (3, cube), (3, cube[:-1]), (3, cube * 4)]
    for _ in range(64):
        n = rng.randint(1, 5)
        formulas.append((n, tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                                       for _ in range(rng.randrange(1, 4)))
                                  for _ in range(rng.randrange(1, 8)))))
    totals = {"sat": 0, "unsat": 0}
    for n, clauses in formulas:
        gates, output = compile_cnf(n, clauses)
        expected = any(accepts_cnf(clauses, x) for x in range(1 << n))
        for budget in (0, 128):
            report = solve(n, gates, output, budget=budget, rewrite_budget=2)
            assert report["status"] == ("sat" if expected else "unsat"), (n, clauses, report)
            if expected:
                assert 0 <= report["witness"] < 1 << n
                assert accepts_cnf(clauses, report["witness"]), (clauses, report)
            totals[report["status"]] += 1
    print(len(formulas), totals, "all original CNF checks passed")


if __name__ == "__main__":
    main()
