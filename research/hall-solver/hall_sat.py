"""Hall-core SAT solver. Input JSON on stdin: {"clauses":[[1,-2]],"core":[2]}."""
from collections import deque
from itertools import product
import json
import sys


def matching(edges):
    """Maximum clause-to-variable matching by successive augmenting paths."""
    assigned = {}
    owner = {}
    for start in range(len(edges)):
        queue = deque([start])
        parent = {}
        while queue:
            clause = queue.popleft()
            for var in edges[clause]:
                if var in parent:
                    continue
                parent[var] = clause
                if var in owner:
                    queue.append(owner[var])
                    continue
                while True:
                    clause = parent[var]
                    previous = assigned.get(clause)
                    assigned[clause] = var
                    owner[var] = clause
                    if previous is None:
                        break
                    var = previous
                queue.clear()
                break
    return assigned, owner


def solve(clauses, core=None):
    rows = []
    variables = set()
    for raw in clauses:
        clause = set(raw)
        if any(type(lit) is not int or lit == 0 for lit in clause):
            raise ValueError("literals must be nonzero signed integers")
        variables.update(map(abs, clause))
        if not any(-lit in clause for lit in clause):
            rows.append(clause)
    edges = [set(map(abs, row)) for row in rows]
    if core is None:
        assigned, owner = matching(edges)
        queue = deque(i for i in range(len(rows)) if i not in assigned)
        core = set()
        while queue:
            for var in edges[queue.popleft()] - core:
                core.add(var)
                queue.append(owner[var])  # Free reachable variable would augment.
    else:
        core = set(core)
        if not core <= variables:
            raise ValueError("supplied core contains absent variables")
        outside = [i for i, e in enumerate(edges) if e - core]
        partial, _ = matching([edges[i] - core for i in outside])
        if len(partial) != len(outside):
            raise ValueError("supplied core admits no saturating outside matching")
        assigned = {outside[j]: v for j, v in partial.items()}
    inside = [row for row, e in zip(rows, edges) if e <= core]
    outside_values = {v: v in rows[i] for i, v in assigned.items() if v not in core}
    tested = 0
    for bits in product((False, True), repeat=len(core)):
        tested += 1
        values = dict(zip(sorted(core), bits))
        if all(any(values[abs(lit)] == (lit > 0) for lit in row) for row in inside):
            values.update(outside_values)
            return result(core, tested, {v: values.get(v, False) for v in variables})
    return result(core, tested, None)


def result(core, tested, model):
    return {"core": sorted(core), "assignments_tested": tested, "model": model}


if __name__ == "__main__":
    print(json.dumps(solve(**json.load(sys.stdin))))
