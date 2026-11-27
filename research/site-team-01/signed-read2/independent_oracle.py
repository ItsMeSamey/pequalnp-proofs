"""Independent signed read-two evaluation oracle and raw-multiset tests. Standard library."""
from collections import Counter
from itertools import combinations_with_replacement, product

def oracle(formula, point):
    """Specialize Boolean pins and count satisfying completions. Return canonical 0,1,2."""
    z = tuple(k % 3 for k in point)
    clauses = tuple(tuple(clause) for clause in formula)
    reads = Counter()
    for clause in clauses:
        for index, sign in clause:
            if not isinstance(index, int) or not 0 <= index < len(z) or sign not in (0, 1):
                raise ValueError("invalid indexed literal")
            reads[index] += 1
    if any(n > 2 for n in reads.values()):
        raise ValueError("variable has more than two literal occurrences")
    free = [i for i, value in enumerate(z) if value == 2]
    bits = list(z)
    count = 0
    for extension in product((0, 1), repeat=len(free)):
        for i, value in zip(free, extension):
            bits[i] = value
        count += all(any(bits[i] == sign for i, sign in clause) for clause in clauses)
    return ((-1) ** len(free) * count) % 3

def corpus():
    literals = list(product(range(2), range(2)))
    clauses = [(literal,) for literal in literals] + list(combinations_with_replacement(literals, 2))
    for length in range(5):
        for formula in combinations_with_replacement(clauses, length):
            reads = Counter(i for clause in formula for i, _ in clause)
            if all(n <= 2 for n in reads.values()):
                yield formula
                yield formula + ((),)

def verify(evaluate):
    # Fixed expectations derived without either algorithm.
    x, nx, y = (0, 1), (0, 0), (1, 1)
    fixtures = [
        ((), (), 1), (((),), (), 0), (((), ()), (), 0),
        ((), (2, 2), 1), (((x, x),), (2,), 2), (((x,), (x,)), (2,), 2),
        (((x, nx),), (2,), 1), (((x,), (nx,)), (2,), 0),
        (((x, y),), (2, 2), 0), (((x, y), (nx, y)), (2, 2), 2),
        (((x, y), (x, y)), (0, 2), 2), (((x, nx), (y,)), (1, 0), 0),
        (((x,),), (1, 2), 1), (((nx,),), (2,), 2)
    ]
    for formula, point, expected in fixtures:
        assert oracle(formula, point) == expected
        assert evaluate(formula, point) == expected, (formula, point, expected)
    families = calls = 0
    for formula in corpus():
        families += 1
        for point in product(range(3), repeat=2):
            expected = oracle(formula, point)
            assert evaluate(formula, point) == expected, (formula, point, expected)
            calls += 1
    assert (families, calls) == (254, 2286)
    return dict(raw_formulas=families, grid_checks=calls, hand_checks=len(fixtures))

if __name__ == '__main__':
    from signed_eval import evaluate
    print(verify(evaluate))
