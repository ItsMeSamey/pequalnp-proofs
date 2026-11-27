"""Source-witness decision for the ordered selector-free ring image."""
from read_two_ring_image import recover


def _reduce(clauses):
    kept = []
    for clause in sorted(set(clauses), key=lambda c: (len(c), tuple(sorted(c)))):
        if not any(old <= clause for old in kept):
            kept.append(clause)
    return kept


def _components(rows):
    incident = {}
    for i, clause in enumerate(rows):
        for lit in clause:
            incident.setdefault(abs(lit), []).append(i)
    seen = set()
    for i in range(len(rows)):
        if i in seen:
            continue
        group = []
        todo = [i]
        seen.add(i)
        while todo:
            j = todo.pop()
            group.append(rows[j])
            for lit in rows[j]:
                for h in incident.pop(abs(lit), ()):
                    if h not in seen:
                        seen.add(h)
                        todo.append(h)
        yield group


def _nested(rows, x):
    scopes = sorted(({abs(lit) for lit in row} for row in rows
                     if x in row or -x in row), key=len)
    return all(a <= b for a, b in zip(scopes, scopes[1:]))


def _project(rows, x):
    pos = [r - {x} for r in rows if x in r]
    neg = [r - {-x} for r in rows if -x in r]
    new = [r for r in rows if x not in r and -x not in r]
    for p in pos:
        for q in neg:
            if not any(-lit in q for lit in p):
                new.append(p | q)
    return _reduce(new), pos, neg


def _component(rows, cap, model):
    if cap is None:
        cap = len(rows)
        if all(len(r) <= 2 for r in rows):
            variables = {abs(lit) for r in rows for lit in r}
            cap = max(cap, 2 * len(variables)**2 + 1)
    if len(rows) > cap:
        return "unknown"
    trail = []
    while rows:
        if not rows[0] or any(not r for r in rows):
            return "zero"
        variables = sorted({abs(lit) for r in rows for lit in r})
        variables.sort(key=lambda x: not _nested(rows, x))
        for x in variables:
            result, pos, neg = _project(rows, x)
            if len(result) <= cap:
                rows = result
                trail.append((x, pos, neg))
                break
        else:
            return "unknown"
    for x, pos, neg in reversed(trail):
        def false_clause(row):
            return not any(model[abs(lit)] == (lit > 0) for lit in row)
        true_needed = any(false_clause(p) for p in pos)
        false_needed = any(false_clause(q) for q in neg)
        if true_needed and false_needed:
            raise AssertionError("inconsistent projected witness")
        model[x] = true_needed
    return "nonzero"


def decide(n, clauses, point, k, *, max_rows=None):
    """A row-cap refusal means unknown. Off-image is a separate outcome."""
    if max_rows is not None and (type(max_rows) is not int or max_rows < 0):
        raise ValueError("max_rows must be a nonnegative integer")
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    a, formula = source
    clean = [frozenset(r) for r in formula if not any(-lit in r for lit in r)]
    rows = _reduce(clean)
    if any(not r for r in rows):
        return dict(status="zero")
    model = [False] * (a+1)
    unknown = False
    for group in _components(rows):
        status = _component(group, max_rows, model)
        if status == "zero":
            return dict(status="zero")
        unknown |= status == "unknown"
    if unknown:
        return dict(status="unknown", reason="row_budget")
    if not all(any(model[abs(lit)] == (lit > 0) for lit in r) for r in formula):
        raise AssertionError("reconstructed witness fails source")
    return dict(status="nonzero", assignment=tuple(map(int, model[1:])))
