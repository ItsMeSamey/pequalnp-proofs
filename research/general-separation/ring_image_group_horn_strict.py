"""Groupwise semantic renamable Horn from explicit forbidden Boolean tuples."""
from collections import defaultdict
from itertools import combinations
from read_two_ring_image import recover


def _groups(groups):
    merged = defaultdict(set)
    for scope, masks in groups:
        scope = tuple(scope)
        if (any(type(x) is not int or x <= 0 for x in scope) or
                len(scope) != len(set(scope))):
            raise ValueError("scopes require distinct positive integer labels")
        order = sorted(range(len(scope)), key=scope.__getitem__)
        target = merged[tuple(scope[i] for i in order)]
        for mask in masks:
            if type(mask) is not int or mask < 0 or mask.bit_length() > len(scope):
                raise ValueError("forbidden mask outside scope")
            target.add(sum(((mask >> i) & 1) << j for j, i in enumerate(order)))
    return merged


def _primes(merged):
    result = set()
    for scope, masks in merged.items():
        cubes = []
        for lo in masks:
            for hi in masks:
                if lo & hi != lo:
                    continue
                size = 1 << (hi ^ lo).bit_count()
                if size > len(masks):
                    continue
                if sum((x & lo == lo and x & hi == x) for x in masks) == size:
                    cubes.append((lo, hi))
        for lo, hi in cubes:
            if any((a, b) != (lo, hi) and a & lo == a and b & hi == hi
                   for a, b in cubes):
                continue
            result.add(tuple(-v if lo >> i & 1 else v for i, v in enumerate(scope)
                             if not ((lo ^ hi) >> i & 1)))
    return tuple(sorted(result))


def prime_kernel(groups):
    """Return all local prime clauses, deduplicated across groups."""
    return _primes(_groups(groups))


def _rename(labels, primes):
    # Flip variable i iff the positive literal +i of this 2-SAT instance is true.
    graph = {s*x: [] for x in labels for s in (1, -1)}
    back = {v: [] for v in graph}
    for clause in primes:
        for a, b in combinations(clause, 2):
            for u, v in ((-a, b), (-b, a)):
                graph[u].append(v)
                back[v].append(u)
    seen = set()
    finish = []
    for start in graph:
        if start in seen:
            continue
        seen.add(start)
        stack = [(start, iter(graph[start]))]
        while stack:
            u, following = stack[-1]
            v = next(following, None)
            if v is None:
                finish.append(u)
                stack.pop()
            elif v not in seen:
                seen.add(v)
                stack.append((v, iter(graph[v])))
    component = {}
    for start in reversed(finish):
        if start in component:
            continue
        tag = len(component)
        component[start] = tag
        todo = [start]
        while todo:
            for v in back[todo.pop()]:
                if v not in component:
                    component[v] = tag
                    todo.append(v)
    if any(component[x] == component[-x] for x in labels):
        return None
    return {x for x in labels if component[x] > component[-x]}


def _label_set(labels):
    variables = set()
    for x in labels:
        if type(x) is not int or x <= 0:
            raise ValueError("labels must be positive integers")
        variables.add(x)
    return variables


def solve_tuples(groups, *, labels=()):
    """Scope[j] is the variable for bit j (LSB first) of each forbidden mask."""
    merged = _groups(groups)
    variables = _label_set(labels)
    variables.update(x for scope in merged for x in scope)
    clauses = _primes(merged)
    flips = _rename(sorted(variables), clauses)
    if flips is None:
        return dict(status="unknown", reason="no_common_horn_renaming")
    rules = []
    for row in clauses:
        signed = [-i if abs(i) in flips else i for i in row]
        heads = [i for i in signed if i > 0]
        if len(heads) > 1:
            raise AssertionError("2-SAT assignment violates Horn renaming")
        rules.append(({-i for i in signed if i < 0}, next(iter(heads), None)))
    true = set()
    while True:
        before = len(true)
        for body, head in rules:
            if body <= true:
                if head is None:
                    return dict(status="zero", flips=tuple(sorted(flips)))
                true.add(head)
        if len(true) == before:
            break
    assignment = {x: int((x in true) != (x in flips)) for x in sorted(variables)}
    for scope, masks in merged.items():
        if sum(assignment[x] << i for i, x in enumerate(scope)) in masks:
            raise AssertionError("Horn witness violates original forbidden tuple")
    return dict(status="nonzero", assignment=assignment, flips=tuple(sorted(flips)))


def solve_sparse(clauses, *, labels=()):
    """Signed one-based literal labels; memory independent of largest label."""
    variables = _label_set(labels)
    original = []
    groups = []
    for raw in clauses:
        row = set()
        for x in raw:
            if type(x) is not int or x == 0:
                raise ValueError("expected signed nonzero integer literals")
            row.add(x)
        variables.update(map(abs, row))
        original.append(row)
        if any(-x in row for x in row):
            continue
        scope = tuple(sorted(map(abs, row)))
        groups.append((scope, [sum(1 << j for j, x in enumerate(scope) if -x in row)]))
    result = solve_tuples(groups, labels=variables)
    if result["status"] == "nonzero":
        assignment = result["assignment"]
        if not all(any(assignment[abs(x)] == (x > 0) for x in row) for row in original):
            raise AssertionError("Horn witness violates source clause")
    return result


def decide(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    a, formula = source
    result = solve_sparse(formula, labels=range(1, a+1))
    if result["status"] == "nonzero":
        values = result["assignment"]
        result["assignment"] = tuple(values[i] for i in range(1, a+1))
    return result
