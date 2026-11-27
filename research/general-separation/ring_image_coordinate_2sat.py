"""Exact affine-coordinate 2SAT for explicit signed CNF and ordered ring images."""
from read_two_ring_image import recover


def _reduce(mask, rhs, rows):
    for pivot in sorted(rows, reverse=True):
        if mask >> pivot & 1:
            row, bit = rows[pivot]
            mask ^= row
            rhs ^= bit
    return mask, rhs


def _insert(mask, rhs, rows):
    mask, rhs = _reduce(mask, rhs, rows)
    if mask:
        rows[mask.bit_length()-1] = (mask, rhs)
    return bool(mask) or rhs == 0


def _lift(rows, word=0):
    for pivot in sorted(rows):
        mask, rhs = rows[pivot]
        if (mask & word).bit_count() % 2 != rhs:
            word ^= 1 << pivot
    return word


def _groups(source):
    blocks = {}
    for row in source:
        lits = set(row)
        if any(-x in lits for x in lits):
            continue
        scope = tuple(sorted(map(abs, lits)))
        forbidden = sum(1 << j for j,x in enumerate(scope) if -x in lits)
        blocks.setdefault(scope, set()).add(forbidden)
    constraints = []
    unsupported = None
    for scope, words in blocks.items():
        anchor = min(words)
        rows = {}
        for word in words:
            _insert(word ^ anchor, 0, rows)
        dim = len(rows)
        if len(words) != 1 << dim:
            unsupported = "nonflat_scope"
            continue
        codim = len(scope) - dim
        if codim == 0:
            return [], "zero"
        if codim > 2:
            unsupported = "codimension"
            continue
        tests = []
        for j in range(len(scope)):
            if j in rows:
                continue
            local = _lift(rows, 1 << j)
            global_mask = sum(1 << (x-1) for t,x in enumerate(scope) if local >> t & 1)
            tests.append((global_mask, (local & anchor).bit_count() % 2))
        constraints.append(tests)
    return constraints, unsupported


def _lines(tests):
    lines = dict(tests)
    if len(tests) == 2:
        (a,b), (c,d) = tests
        lines[a ^ c] = b ^ d
    return lines


def coordinate_axes(constraints):
    """Return independent axes spanning each singleton/plane by a subset."""
    spaces = {frozenset(_lines(tests)) for tests in constraints}
    forced = {next(iter(space)) for space in spaces if len(space) == 1}
    seen = set()
    planes = sorted((s for s in spaces if len(s) == 3), key=lambda s: sorted(s))
    for space in planes:
        forced.update(space & seen)
        seen.update(space)
    axes = set(forced)
    for space in planes:
        shared = space & forced
        if len(shared) > 2:
            return None
        axes.update(sorted(space - shared)[:2-len(shared)])
    rows = {}
    for axis in axes:
        _insert(axis, 0, rows)
    return sorted(axes) if len(rows) == len(axes) else None


def _finish_order(graph):
    seen = set()
    order = []
    for root in range(len(graph)):
        if root in seen:
            continue
        stack = [(root, iter(graph[root]))]
        seen.add(root)
        while stack:
            v, children = stack[-1]
            w = next(children, None)
            if w is None:
                order.append(v)
                stack.pop()
            elif w not in seen:
                seen.add(w)
                stack.append((w, iter(graph[w])))
    return order


def _two_sat(axes, constraints):
    ids = {a:i for i,a in enumerate(axes)}
    graph = [[] for _ in range(2 * len(axes))]
    reverse = [[] for _ in graph]
    for tests in constraints:
        lines = _lines(tests)
        literals = [2*ids[a] + (1-b) for a,b in lines.items() if a in ids]
        assert len(literals) == len(tests)
        for a,b in ((literals[0], literals[-1]), (literals[-1], literals[0])):
            graph[a ^ 1].append(b)
            reverse[b].append(a ^ 1)
    comp = [-1] * len(graph)
    for label, root in enumerate(reversed(_finish_order(graph))):
        if comp[root] >= 0:
            continue
        stack = [root]
        comp[root] = label
        while stack:
            for w in reverse[stack.pop()]:
                if comp[w] == -1:
                    comp[w] = label
                    stack.append(w)
    if any(comp[2*i] == comp[2*i+1] for i in range(len(axes))):
        return None
    return [int(comp[2*i+1] > comp[2*i]) for i in range(len(axes))]


def _quotient(constraints):
    equations = {}
    while True:
        remaining = []
        added = False
        for tests in constraints:
            local = {}
            for a,b in tests:
                a,b = _reduce(a,b,equations)
                if not _insert(a,b,local):
                    break  # The forbidden conjunction is already impossible.
            else:
                reduced = list(local.values())
                if not reduced:
                    return None, None
                if len(reduced) == 1:
                    a,b = reduced[0]
                    _insert(a,1-b,equations)
                    added = True
                else:
                    remaining.append(reduced)
        constraints = remaining
        if not added:
            return equations, constraints


def solve_source(arity, signed_clauses):
    """Return zero, nonzero with assignment, or unknown; costs poly(arity+input)."""
    if type(arity) is not int or arity < 0:
        raise ValueError("invalid arity")
    source = tuple(tuple(row) for row in signed_clauses)
    if any(type(x) is not int or not 1 <= abs(x) <= arity for row in source for x in row):
        raise ValueError("invalid signed literal")
    constraints, reason = _groups(source)
    if reason == "zero":
        return dict(status="zero")
    if reason:
        return dict(status="unknown", reason=reason)
    equations = {}
    axes = coordinate_axes(constraints)
    if axes is None:
        equations, constraints = _quotient(constraints)
        if equations is None:
            return dict(status="zero")
        axes = coordinate_axes(constraints)
        if axes is None:
            return dict(status="unknown", reason="incompatible_axes")
    bits = _two_sat(axes, constraints)
    if bits is None:
        return dict(status="zero")
    for axis, bit in zip(axes, bits):
        if not _insert(axis, bit, equations):
            raise AssertionError("inconsistent chart lift")
    word = _lift(equations)
    assignment = tuple(word >> i & 1 for i in range(arity))
    if not all(any(assignment[abs(x)-1] == int(x > 0) for x in row) for row in source):
        raise AssertionError("invalid lifted witness")
    return dict(status="nonzero", assignment=assignment)


def solve(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    return solve_source(*source)
