"""Linear-size encoding from signed 3-CNF to paired forbidden bits and parity checks."""
from kernel.kernel import solve


def encode(clauses):
    pairs = []
    previous = {}
    target = 0
    rows = 0
    for clause in clauses:
        if len(clause) != 3 or any(lit == 0 for lit in clause):
            raise ValueError("expected three nonzero signed literals")
        clause_row = 1 << rows
        target |= clause_row
        rows += 1
        for lit in clause:
            variable = abs(lit)
            occurrence = len(pairs)
            pairs.append([0, clause_row])
            if variable in previous:
                old, old_literal = previous[variable]
                row = 1 << rows
                rows += 1
                pairs[old][0] |= row
                pairs[occurrence][0] |= row
                if (lit < 0) != (old_literal < 0):
                    target |= row
            previous[variable] = occurrence, lit
    return pairs, target


def search(clauses):
    pairs, target = encode(clauses)
    choices = solve(pairs, target)
    if choices is None:
        return None
    assignment = {}
    for clause_index, clause in enumerate(clauses):
        for i, lit in enumerate(clause):
            false = choices[3 * clause_index + i] == 1
            value = false if lit < 0 else not false
            if abs(lit) in assignment:
                assert assignment[abs(lit)] == value
            assignment[abs(lit)] = value
    return assignment


if __name__ == '__main__':
    from itertools import product
    from random import Random

    def satisfies(clauses, assignment):
        return all(any(assignment[abs(lit)] == (lit > 0) for lit in c) for c in clauses)

    rng = Random(7919)
    examples = [[], [(1,1,1),(-1,-1,-1)]]
    for _ in range(300):
        n = rng.randrange(1, 7)
        lits = [v * sign for v in range(1, n + 1) for sign in (-1, 1)]
        examples.append([tuple(rng.choices(lits, k=3)) for _ in range(rng.randrange(1, 6))])
    for clauses in examples:
        assignment = search(clauses)
        names = sorted({abs(lit) for c in clauses for lit in c})
        feasible = any(satisfies(clauses, dict(zip(names, bits))) for bits in product((False, True), repeat=len(names)))
        assert (assignment is not None) == feasible
        if feasible:
            assert satisfies(clauses, assignment)
    print(len(examples))
