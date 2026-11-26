"""Discover source choices when every cover has length at least three."""
from choice_cover_one_xor import solve


def solve_long_covers(n, clauses, xor_literals, rhs):
    """Return the validated solver result. Unsupported syntax raises ValueError."""
    clauses = [tuple(dict.fromkeys(row)) for row in clauses]
    covers = [i for i, row in enumerate(clauses) if len(row) >= 3]
    return solve(n, clauses, covers, xor_literals, rhs)
