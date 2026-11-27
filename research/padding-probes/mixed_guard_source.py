"""Coupled SAT/UNSAT original CNFs with one admissible nonbijunctive shared-pair interval."""


def guard_source(h=1, *, satisfiable=True):
    """Return (n, source clauses). The positive member has exactly 3^(3h) models."""
    if type(h) is not int or h < 1 or type(satisfiable) is not bool:
        raise ValueError("expected positive repetitions and Boolean choice")
    rows = []
    for i in range(4 * h):
        y = 3 + 3 * i
        z, w = y + 1, y + 2
        rows.extend(((1 if i & 1 else -1, 2 if i & 2 else -2, y),
                     (-y, z), (-z, w), (-w, y if satisfiable and i % 4 == 1 else -y)))
    return 12 * h + 2, tuple(rows)


def positive_true_ids(h=1):
    """A satisfying original assignment for guard_source(h,satisfiable=True)."""
    if type(h) is not int or h < 1:
        raise ValueError("positive repetitions required")
    true = [2]
    for i in range(1, 4 * h, 4):
        true.extend((3 + 3 * i, 4 + 3 * i, 5 + 3 * i))
    return tuple(true)
