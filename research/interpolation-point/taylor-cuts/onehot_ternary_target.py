"""Decision-only ternary frame stage for signed synchronized one-hot CNF+XOR."""
from onehot_colour_folds import recognize
from ternary_frame import color


def decide(n, clauses, equations, *, state_cap, use_prism=True):
    if type(state_cap) is not int or state_cap < 0:
        raise ValueError("state_cap must be a nonnegative integer")
    clauses = tuple(tuple(row) for row in clauses)
    equations = tuple(equations)
    parsed = recognize(n, clauses, equations)
    if parsed is None:
        return "UNKNOWN", None, {"reason": "unrecognized source"}
    names, graph = parsed
    edges = [(u, v) for u, neighbors in graph.items() for v in neighbors if u < v]
    status, coloring, stats = color(len(names), edges, cap=state_cap, use_prism=use_prism)
    if coloring is None:
        return status, None, stats
    witness = 0
    for vertex, palette in enumerate(names):
        for index, literal in enumerate(palette):
            if (index == coloring[vertex]) != (literal < 0):
                witness |= 1 << (abs(literal) - 1)
    for row in clauses:
        if not any(bool(witness & (1 << (abs(lit) - 1))) == (lit > 0) for lit in row):
            raise ArithmeticError("coloring witness violates an original clause")
    if any((mask & witness).bit_count() % 2 != rhs for mask, rhs in equations):
        raise ArithmeticError("coloring witness violates an original parity")
    return status, witness, stats
