"""Solve arbitrary signed 2-CNF plus parity rows by translating a 2-SAT model."""
from affine_projective_layer import _two_sat
from horn_closure_xor import solve_horn_xor


def solve_two_sat_xor(n, signed_clauses, xor_rows):
    """Return an assignment bitmask or None. Literals are signed and one-based."""
    if not isinstance(n, int) or n < 0:
        raise ValueError("invalid variable count")
    clauses = [tuple(clause) for clause in signed_clauses]
    rows = list(xor_rows)
    for clause in clauses:
        if len(clause) > 2 or any(not isinstance(lit, int) or not 1 <= abs(lit) <= n
                                  for lit in clause):
            raise ValueError("invalid 2-CNF clause")
    for mask, rhs in rows:
        if not isinstance(mask, int) or mask < 0 or mask >> n or rhs not in (0, 1):
            raise ValueError("invalid parity row")
    if any(not clause for clause in clauses):
        return None
    binary = []
    for clause in clauses:
        literals = [2*(abs(lit)-1) + (lit > 0) for lit in clause]
        binary.append((literals[0], literals[-1]))
    model = _two_sat(n, binary)
    if model is None:
        return None
    baseline = sum(1 << i for i, value in enumerate(model) if value)
    flipped = [[-lit if model[abs(lit)-1] else lit for lit in clause]
               for clause in clauses]
    translated = [(mask, rhs ^ ((mask & baseline).bit_count() & 1))
                  for mask, rhs in rows]
    toggle = solve_horn_xor(n, flipped, translated)
    return None if toggle is None else baseline ^ toggle
