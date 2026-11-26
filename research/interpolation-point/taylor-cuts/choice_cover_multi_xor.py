"""Signed CNF+XOR frontend to the parity SCC certificate and exact fallback."""
from choice_cover_one_xor import prepare, initial_matching, decode
from parity_scc_peel import peel


def solve(n, clauses, covers, equations, *, exact=False):
    """Return (SAT/UNSAT/UNKNOWN, original assignment or None, stalled rows).

    Pass exact=True for a complete (potentially exponential) decision.
    Every returned SAT assignment is checked against the original source.
    """
    clauses = tuple(tuple(c) for c in clauses)
    equations = tuple((tuple(lits), rhs) for lits, rhs in equations)
    problem = prepare(n, clauses, covers, equations)
    if problem is None:
        return 'UNSAT', None, []
    options, target, free, signed = problem
    base = initial_matching(options)
    if base is None:
        return 'UNSAT', None, []
    status, chosen, free_word, stalled = peel(options, base, target,
                                             [mask for _,mask in free], exact=exact)
    if status != 'SAT':
        return status, None, stalled
    return status, decode(chosen, signed, free, free_word, clauses, equations), stalled


def solve_long_covers(n, clauses, equations, *, exact=False):
    """Infer the choice clauses when all have at least three distinct literals."""
    clauses = tuple(tuple(dict.fromkeys(c)) for c in clauses)
    covers = [i for i,c in enumerate(clauses) if len(c)>=3]
    return solve(n, clauses, covers, equations, exact=exact)
