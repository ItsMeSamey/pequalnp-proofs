"""Compare the signed wrapper with exhaustive assignment enumeration."""
from itertools import combinations, combinations_with_replacement, product
from random import Random

from two_sat_xor import solve_two_sat_xor


def check(n, clauses, rows):
    def valid(x):
        return all(any(bool(x & (1 << (abs(lit)-1))) == (lit > 0) for lit in clause)
                   for clause in clauses) and all((mask & x).bit_count() % 2 == rhs
                                                  for mask, rhs in rows)
    actual = solve_two_sat_xor(n, clauses, rows)
    expected = next((x for x in range(1 << n) if valid(x)), None)
    assert (actual is None) == (expected is None), (n, clauses, rows, actual, expected)
    assert actual is None or valid(actual), (clauses, rows, actual)


def main():
    count = 0
    n = 2
    literals = (-2, -1, 1, 2)
    clauses = [(), *((v,) for v in literals), *combinations_with_replacement(literals, 2)]
    choices = [(), *((c,) for c in clauses), *combinations_with_replacement(clauses, 2)]
    rows = list(product(range(4), (0, 1)))
    row_sets = [(), *((r,) for r in rows), *combinations_with_replacement(rows, 2)]
    for cs, rs in product(choices, row_sets):
        check(n, cs, rs)
        count += 1
    rng = Random(58491)
    for _ in range(2000):
        n = rng.randrange(9)
        cs = [tuple(rng.choice((-1, 1)) * rng.randrange(1, n+1)
                    for _ in range(rng.choice((1, 2, 2)))) for _ in range(rng.randrange(14))] if n else []
        rs = [(rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(7))]
        check(n, cs, rs)
        count += 1
    for _ in range(150):
        n, k = rng.randrange(1, 6), rng.randrange(1, 4)
        pairs = list(combinations(range(n), 2))
        edges = {pair for pair in pairs if rng.randrange(2)}
        allowed = any(all(pair in edges for pair in combinations(group, 2))
                      for group in combinations(range(n), k))
        positions = list(product(range(k), range(n)))
        conflicts = []
        for i, j in combinations(range(len(positions)), 2):
            c, u = positions[i]
            d, v = positions[j]
            if c == d or tuple(sorted((u, v))) not in edges:
                conflicts.append((-(i+1), -(j+1)))
        rows = [(((1 << n)-1) << (c*n), 1) for c in range(k)]
        witness = solve_two_sat_xor(n*k, conflicts, rows)
        assert (witness is not None) == allowed
    print(f"{count} brute-force comparisons and 150 clique reductions passed")


if __name__ == "__main__":
    main()
