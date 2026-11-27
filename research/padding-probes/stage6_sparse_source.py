"""A sparse-name original CNF entry point with an original-label witness."""
from collections.abc import Mapping
from stage6_normalized_solver import solve as solve_dense


def solve(n, clauses, *, source_pins=(), exact_twice=False, stages=None, fallback_limit=0):
    """Return the sorted true variable names; all other declared names are false."""
    if type(n) is not int or n < 0:
        raise ValueError("invalid declared variable count")
    clauses = tuple(tuple(row) for row in clauses)
    if any(len(row) > 3 or any(type(x) is not int or not 1 <= abs(x) <= n for x in row)
           for row in clauses):
        raise ValueError("expected signed clauses of width at most three")
    pins = tuple(source_pins.items() if isinstance(source_pins, Mapping) else source_pins)
    if any(type(x) is not int or not 1 <= x <= n or type(b) is not int or b not in (0, 1)
           for x, b in pins):
        raise ValueError("invalid source pin")
    names = sorted({abs(x) for row in clauses for x in row} | {x for x, _ in pins})
    index = {name: i for i, name in enumerate(names, 1)}
    rows = [tuple(index[x] if x > 0 else -index[-x] for x in row) for row in clauses]
    result = solve_dense(len(names), rows, source_pins=[(index[x], b) for x, b in pins],
                         exact_twice=exact_twice, stages=stages, fallback_limit=fallback_limit)
    mask = result.pop("witness")
    result.pop("sparse_witness")
    result["true_variables"] = None
    if result["status"] == "SAT":
        selected = tuple(name for i, name in enumerate(names) if (mask >> i) & 1)
        true = set(selected)
        if (any(not any((abs(x) in true) == (x > 0) for x in row) for row in clauses) or
                any((x in true) != bool(b) for x, b in pins)):
            raise ArithmeticError("original sparse assignment failed")
        result["true_variables"] = selected
    return result
