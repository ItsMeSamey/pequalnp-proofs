"""Decide SAT on formulas of maximum deficiency at most one."""
from collections import deque
from hall_sat import matching


def extend(edges, assigned):
    """Complete a partial matching if possible, with one BFS per exposed clause."""
    owner = {v: c for c, v in assigned.items()}
    for start in edges:
        if start in assigned:
            continue
        parent = {}
        queue = deque([start])
        while queue:
            c = queue.popleft()
            for v in edges[c]:
                if v in parent:
                    continue
                parent[v] = c
                if v in owner:
                    queue.append(owner[v])
                    continue
                while True:
                    c = parent[v]
                    old = assigned.get(c)
                    assigned[c] = v
                    owner[v] = c
                    if old is None:
                        break
                    v = old
                queue.clear()
                break
        if start not in assigned:
            return False
    return True


def solve_deficiency_one(clauses):
    """Return a Boolean model, None for UNSAT, or raise if outside the promise."""
    raw = [frozenset(clause) for clause in clauses]
    if any(type(lit) is not int or lit == 0 for row in raw for lit in row):
        raise ValueError("literals must be nonzero signed integers")
    variables = {abs(lit) for row in raw for lit in row}
    rows = list(dict.fromkeys(row for row in raw if not any(-lit in row for lit in row)))
    edges = [set(map(abs, row)) for row in rows]
    assigned, _ = matching(edges)
    deficiency = len(rows) - len(assigned)
    if deficiency > 1:
        raise ValueError("normalized formula has maximum deficiency above one")
    if deficiency == 0:
        model = dict.fromkeys(variables, False)
        model.update({v: v in rows[c] for c, v in assigned.items()})
        return model
    candidates = {lit for row in rows for lit in row}
    for lit in candidates:
        v = abs(lit)
        residual = {c: edge - {v} for c, edge in enumerate(edges) if lit not in rows[c]}
        partial = {c: w for c, w in assigned.items() if c in residual and w != v}
        if extend(residual, partial):
            model = dict.fromkeys(variables, False)
            model[v] = lit > 0
            model.update({w: w in rows[c] for c, w in partial.items()})
            return model
    return None
