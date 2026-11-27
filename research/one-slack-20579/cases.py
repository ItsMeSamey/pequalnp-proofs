"""Verify the frozen CNF for the five abstract one-slack cases."""

from itertools import combinations
from pathlib import Path


def _has_model(clauses):
    """Decide the small residual formula by unit propagation and splitting."""
    while clauses:
        if any(not clause for clause in clauses):
            return False
        unit = next((c[0] for c in clauses if len(c) == 1), None)
        if unit is None:
            pivot = clauses[0][0]
            return any(_has_model([[lit]] + clauses) for lit in (pivot, -pivot))
        clauses = [[v for v in c if v != -unit] for c in clauses if unit not in c]
    return True


def verify_cases(path, bank, triangle):
    """Check cases.cnf against the supplied bank and checked triangle."""
    bank = tuple(bank)
    if len(bank) != 15 or len(set(bank)) != 15:
        raise ValueError("expected fifteen distinct bank wires")
    triangle = tuple(triangle)
    if len(triangle) != 3:
        raise ValueError("expected three triangle vertices or edges")
    if all(isinstance(item, int) for item in triangle):
        edges = list(combinations(triangle, 2))
    else:
        edges = [tuple(item["pair"] if isinstance(item, dict) else item)
                 for item in triangle]
    vertices = {wire for edge in edges for wire in edge}
    if len(vertices) != 3 or not vertices.issubset(bank):
        raise ValueError("invalid triangle vertices")
    ordered = [wire for wire in bank if wire in vertices]
    pairs = list(combinations(ordered, 2))
    if {frozenset(edge) for edge in edges} != {frozenset(pair) for pair in pairs}:
        raise ValueError("incomplete triangle")

    zero, dead, missing, invert, fork = range(1, 6)
    negative = {wire: 6 + i for i, wire in enumerate(bank)}
    duplicate = {wire: 21 + i for i, wire in enumerate(bank)}
    clauses = [[zero, dead, missing, invert, fork], [-zero], [-dead], [-missing]]
    clauses.append([-invert, *negative.values()])
    clauses.extend([-invert, -var] for var in negative.values())
    for left, right in pairs:
        a, b = duplicate[left], duplicate[right]
        clauses.extend(([-fork, a, b], [-fork, -a, -b]))

    variables = max(abs(lit) for clause in clauses for lit in clause)
    expected = [f"p cnf {variables} {len(clauses)}"]
    expected.extend(" ".join(map(str, (*clause, 0))) for clause in clauses)
    if Path(path).read_bytes() != ("\n".join(expected) + "\n").encode("ascii"):
        raise ValueError("frozen DIMACS differs from reconstructed cases")
    if _has_model(clauses):
        raise ValueError("the reconstructed necessary clauses admit a model")
    return True
