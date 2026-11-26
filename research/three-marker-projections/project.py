"""Extract feasible three-bit labels using two-marker witnesses on all pairs."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

spec = spec_from_file_location("two_marker_solver",
                               Path(__file__).resolve().parents[1] / "two-markers" / "check.py")
two = module_from_spec(spec)
spec.loader.exec_module(two)


def parity(value):
    return value.bit_count() & 1


def label(columns, support):
    value = 0
    for i, c in enumerate(columns):
        if support >> i & 1:
            value ^= c
    return value


def pair_queries(rows, columns):
    """Return a witness dict and a set certified absent. At most one is undecided."""
    found = {}
    absent = set()
    for direction in range(1, 8):
        a, b, _ = [v for v in range(1, 8) if not parity(v & direction)]
        def quotient(value):
            return parity(value & a) | (parity(value & b) << 1)
        projected = [quotient(c) for c in columns]
        for target in range(4):
            x = two.witness(rows, projected, target)
            if x is None:
                absent.update(c for c in range(8) if quotient(c) == target)
            else:
                found[label(columns, x)] = x
    return found, absent


def active_components(rows, columns):
    unseen = set(range(len(rows)))
    while unseen:
        stack = [unseen.pop()]
        vertices = []
        while stack:
            i = stack.pop()
            vertices.append(i)
            neighbors = {j for j in unseen if rows[i] >> j & 1}
            unseen -= neighbors
            stack.extend(neighbors)
        if any(columns[i] for i in vertices):
            yield vertices


def component_tables(rows, columns):
    """Return all determined answers and witnesses, with at most one unanswered."""
    pieces = []
    for vertices in active_components(rows, columns):
        local = [sum((rows[i] >> j & 1) << k for k,j in enumerate(vertices))
                 for i in vertices]
        found, absent = pair_queries(local, [columns[i] for i in vertices])
        lifted = {out: sum((x >> k & 1) << j for k,j in enumerate(vertices))
                  for out,x in found.items()}
        pieces.append((lifted, absent))
    if len(pieces) == 1:
        return pieces[0]
    table = {0: 0}
    for found, _ in pieces:
        table = {a ^ b: x | y for a,x in table.items() for b,y in found.items()}
    return table, set(range(8)) - table.keys()
