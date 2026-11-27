"""Polynomial source-CNF prepass returning original-coordinate witnesses."""
from collections import defaultdict, deque
from collections.abc import Mapping
from itertools import combinations


def _binary(clauses):
    """Solve clauses of size one or two using iterative Kosaraju SCCs."""
    out = defaultdict(list)
    rev = defaultdict(list)
    for clause in clauses:
        a, b = clause[0], clause[-1]
        for u, v in ((-a, b), (-b, a)):
            out[u].append(v)
            rev[v].append(u)
    nodes = set(out) | set(rev)
    seen = set()
    order = []
    for root in nodes:
        if root in seen:
            continue
        seen.add(root)
        todo = [(root, iter(out[root]))]
        while todo:
            v, edges = todo[-1]
            u = next(edges, None)
            if u is None:
                todo.pop()
                order.append(v)
            elif u not in seen:
                seen.add(u)
                todo.append((u, iter(out[u])))
    comp = {}
    for index, root in enumerate(reversed(order)):
        if root in comp:
            continue
        comp[root] = index
        todo = [root]
        while todo:
            for u in rev[todo.pop()]:
                if u not in comp:
                    comp[u] = index
                    todo.append(u)
    names = {abs(v) for v in nodes}
    if any(comp[v] == comp[-v] for v in names):
        return None
    return {v: int(comp[v] > comp[-v]) for v in names}


def _horn(clauses):
    """Compute the least Horn model; integrity constraints have no head."""
    waiting = defaultdict(list)
    remaining = []
    heads = []
    ready = deque()
    for row in clauses:
        body = [-v for v in row if v < 0]
        head = next((v for v in row if v > 0), None)
        i = len(heads)
        remaining.append(len(body))
        heads.append(head)
        for v in body:
            waiting[v].append(i)
        if not body:
            ready.append(head)
    true = set()
    while ready:
        v = ready.popleft()
        if v is None:
            return None
        if v in true:
            continue
        true.add(v)
        for i in waiting[v]:
            remaining[i] -= 1
            if not remaining[i]:
                ready.append(heads[i])
    return true


def solve_prepass(n, clauses, *, pins=()):
    """Return (SAT, mask, route), (UNSAT, None, route), or (UNKNOWN, None, route).

    The mask uses bit v-1 for dense source variable v. Clauses may have any
    width; generating the renaming instance takes the sum of squared widths.
    """
    if type(n) is not int or n < 0:
        raise ValueError("invalid declared variable count")
    rows = []
    for clause in clauses:
        literals = tuple(clause)
        if any(type(v) is not int or not 1 <= abs(v) <= n for v in literals):
            raise ValueError("invalid source literal")
        row = set(literals)
        if not any(-v in row for v in row):
            rows.append(row)
    pins = tuple(pins.items() if isinstance(pins, Mapping) else pins)
    if any(type(v) is not int or not 1 <= v <= n or type(b) is not int or b not in (0, 1)
           for v, b in pins):
        raise ValueError("invalid source pin")
    fixed = dict(pins)
    if any(fixed[v] != b for v, b in pins):
        return "UNSAT", None, "pins"

    def sat(values, route):
        mask = sum(1 << (v-1) for v, b in (fixed | values).items() if b)
        return "SAT", mask, route

    new = fixed.copy()
    while True:
        false = {-v if b else v for v, b in new.items()}
        true = {-v for v in false}
        rows = [row-false for row in rows if row.isdisjoint(true)]
        if not rows:
            return sat({}, "simplify")
        if any(not row for row in rows):
            return "UNSAT", None, "simplify"
        units = {next(iter(row)) for row in rows if len(row) == 1}
        if any(-v in units for v in units):
            return "UNSAT", None, "simplify"
        literals = set().union(*rows)
        pure = {v for v in literals if -v not in literals}
        new = {abs(v): int(v > 0) for v in units | pure}
        if not new:
            break
        fixed.update(new)
    if all(len(row) <= 2 for row in rows):
        values = _binary(tuple(row) for row in rows)
        if values is None:
            return "UNSAT", None, "2sat"
        return sat(values, "2sat")
    # Flip variable v if its renaming bit is one. In each pair, at least
    # one original literal must become negative under the chosen flip.
    flips = _binary(pair for row in rows for pair in combinations(row, 2))
    if flips is None:
        return "UNKNOWN", None, "non-renamable"
    renamed = [tuple(-v if flips.get(abs(v), 0) else v for v in row) for row in rows]
    true = _horn(renamed)
    if true is None:
        return "UNSAT", None, "renamable-horn"
    values = {abs(v): int(abs(v) in true) ^ flips.get(abs(v), 0) for v in literals}
    return sat(values, "renamable-horn")
