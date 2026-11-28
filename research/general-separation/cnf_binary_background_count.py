"""Exact sparse CNF count using restricted misses and a binary forest."""
from itertools import product
import cnf_binary_background_rank as restricted
import cnf_miss_span


class _Exhausted(Exception):
    pass


def _forest(names, binary):
    graph = {v: set() for v in names}
    for row in binary:
        if len(row) == 2:
            x, y = map(abs, row)
            graph[x].add(y)
            graph[y].add(x)
    core = {x: adjacent.copy() for x, adjacent in graph.items()}
    cut = []
    while core:
        leaf = next((x for x in core if len(core[x]) <= 1), None)
        if leaf is None:
            leaf = min(core, key=lambda x: (-len(core[x]), x))
            cut.append(leaf)
        for y in core.pop(leaf):
            core[y].remove(leaf)
    omitted = set(cut)
    parents = {}
    order = []
    for root in names:
        if root in omitted or root in parents:
            continue
        parents[root] = None
        todo = [root]
        while todo:
            x = todo.pop()
            order.append(x)
            for y in graph[x] - omitted:
                if y == parents[x]:
                    continue
                if y in parents:
                    raise AssertionError("feedback set leaves a cycle")
                parents[y] = x
                todo.append(y)
    return tuple(cut), parents, order


def _tree_count(binary, pins, parents, order):
    table = {x: [1, 1] for x in order}
    forbidden_pairs = {}
    for raw in binary:
        if any(pins.get(abs(i)) == (i > 0) for i in raw):
            continue
        row = [i for i in raw if abs(i) not in pins]
        if not row:
            return 0
        if len(row) == 1:
            i, = row
            table[abs(i)][int(i < 0)] = 0
        else:
            i, j = row
            x, y = abs(i), abs(j)
            if parents[x] != y:
                x, y, i, j = y, x, j, i
            if parents[x] != y:
                raise AssertionError("uncertified binary interaction")
            forbidden_pairs.setdefault(x, set()).add((int(i < 0), int(j < 0)))
    for x in order:
        if x in pins:
            table[x][1-int(pins[x])] = 0
    total = 1
    for x in reversed(order):
        p = parents[x]
        if p is None:
            total *= sum(table[x])
        else:
            forbidden = forbidden_pairs.get(x, ())
            for bit in (0, 1):
                table[p][bit] *= sum(table[x][v] for v in (0, 1)
                                     if (v, bit) not in forbidden)
    return total


def solve(arity, clauses, *, max_terms=None):
    if max_terms is not None and (type(max_terms) is not int or max_terms < 0):
        raise ValueError("invalid term budget")
    if type(arity) is not int or arity < 0:
        raise ValueError("invalid arity")
    original = tuple(tuple(row) for row in clauses)
    if any(type(i) is not int or not 1 <= abs(i) <= arity for row in original for i in row):
        raise ValueError("invalid signed literal")
    if any(len(set(row)) > 3 and not any(-i in row for i in row) for row in original):
        answer = cnf_miss_span.solve(arity, original, max_terms=max_terms)
        return dict(answer, backend="unrestricted_span")
    basis = restricted.project(arity, original)
    free = arity - len(basis.used)
    if not basis.feasible:
        return dict(status="zero", count=(0, free), terms=0, rank=0, feedback=0, feedback_vertices=(),
                    mode="infeasible_background", backend="binary_background")
    binary, residual = tuple(basis.background), tuple(basis.clauses)
    names = sorted({abs(i) for row in binary + residual for i in row})
    cut, parents, order = _forest(names, binary)
    h, f, k = len(names), len(cut), len(residual)
    enum = (1 << h) <= ((h+1) << (k+f))
    stats = dict(terms=0, rank=k, feedback=f, feedback_ids=cut, feedback_vertices=cut,
                 mode="enumerate" if enum else "forest", backend="binary_background")

    def charge():
        if max_terms is not None and stats["terms"] >= max_terms:
            raise _Exhausted
        stats["terms"] += 1

    def conditional(fixed):
        total = 0
        for subset in range(1 << k):
            forced = dict(fixed)
            conflict = False
            for j, row in enumerate(residual):
                if subset >> j & 1:
                    for i in row:
                        bit = i < 0
                        if forced.setdefault(abs(i), bit) != bit:
                            conflict = True
            if conflict:
                charge()
                continue
            for word in product((False, True), repeat=f):
                charge()
                if any(x in forced and forced[x] != bit for x, bit in zip(cut, word)):
                    continue
                pins = dict(forced)
                pins.update(zip(cut, word))
                mass = _tree_count(binary, pins, parents, order)
                total += -mass if subset.bit_count() % 2 else mass
        return total

    try:
        model = set()
        if enum:
            total = 0
            for word in product((False, True), repeat=h):
                charge()
                bits = dict(zip(names, word))
                if all(any(bits[abs(i)] == (i > 0) for i in row) for row in binary + residual):
                    if not total:
                        model = {i for i in names if bits[i]}
                    total += 1
        else:
            total = conditional({})
            if total:
                fixed = {}
                for x in names:
                    fixed[x] = False
                    if conditional(fixed) == 0:
                        fixed[x] = True
                        model.add(x)
    except _Exhausted:
        return dict(stats, status="unknown", reason="count_budget",
                    required=stats["terms"]+1, available=max_terms)
    answer = dict(stats, status="nonzero" if total else "zero",
                  count=(total << (len(basis.used)-h), free))
    if total:
        if not all(any((abs(i) in model) == (i > 0) for i in row) for row in original):
            raise AssertionError("invalid original source witness")
        answer["true_ids"] = tuple(sorted(model))
    return answer


count = solve
