"""Exact affine hulls of 2-SAT models and certified multi-XOR peeling."""
from functools import reduce
from operator import xor


def reachable(root, graph):
    seen = {root}
    todo = [root]
    while todo:
        for v in graph[todo.pop()]:
            if v not in seen:
                seen.add(v)
                todo.append(v)
    return seen


def image(mask, labels):
    return reduce(xor, (v for i, v in enumerate(labels) if mask >> i & 1), 0)


def reduce_vector(value, basis):
    tag = 0
    for k in sorted(basis, reverse=True):
        if value >> k & 1:
            v, w = basis[k]
            value ^= v
            tag ^= w
    return value, tag


def add_vector(value, tag, basis):
    remainder, used = reduce_vector(value, basis)
    if remainder:
        basis[remainder.bit_length()-1] = (remainder, tag ^ used)


def prepare(n, clauses):
    """Return a baseline and, by independent block, (direction, adjacent models)."""
    if type(n) is not int or n < 0:
        raise ValueError("invalid variable count")
    literals = [s*i for i in range(1,n+1) for s in (1,-1)]
    graph = {lit: set() for lit in literals}
    coupling = {i: set() for i in range(1,n+1)}
    empty = False
    for clause in clauses:
        row = list(dict.fromkeys(clause))
        if any(type(v) is not int or not 1 <= abs(v) <= n for v in row):
            raise ValueError("invalid literal")
        if any(-v in row for v in row):
            continue
        if len(row) > 2:
            raise ValueError("expected 2-CNF")
        if not row:
            empty = True
            continue
        a, b = row[0], row[-1]
        graph[-a].add(b)
        graph[-b].add(a)
        coupling[abs(a)].add(abs(b))
        coupling[abs(b)].add(abs(a))
    if empty:
        return None
    reach = {v: reachable(v, graph) for v in literals}
    if any(-v in reach[v] and v in reach[-v] for v in literals):
        return None

    def extend(pins):
        assigned = set().union(*(reach[v] for v in pins))
        if any(-v in assigned for v in assigned):
            raise AssertionError("inconsistent promised pins")
        for i in range(1, n+1):
            if i in assigned or -i in assigned:
                continue
            candidate = assigned | reach[-i]
            if any(-v in candidate for v in candidate):
                assigned.update(reach[i])
            else:
                assigned = candidate
        return sum(1 << (i-1) for i in assigned if i > 0)

    base = extend(())
    blocks = []
    done = set()
    for i in range(1, n+1):
        if i in done:
            continue
        variables = reachable(i, coupling)
        done.update(variables)
        blockmask = sum(1 << (v-1) for v in variables)
        pairs = []
        covered = set()
        for v in sorted(variables):
            if v in covered:
                continue
            c = {w for w in reach[v] if v in reach[w]}
            covered.update(abs(w) for w in c)
            if -v in reach[v] or v in reach[-v]:
                continue
            opposite = {-w for w in c}
            pins = (reach[v] - c) | (reach[-v] - opposite) | {v}
            first = extend(pins) & blockmask
            delta = sum(1 << (abs(w)-1) for w in c)
            pairs.append((delta, first, first ^ delta))
        blocks.append((blockmask, pairs))
    return base, blocks


def image_hull(prepared, labels):
    """Return a point and a binary echelon basis of the attainable label hull."""
    if prepared is None:
        return None
    base, blocks = prepared
    basis = {}
    for _, pairs in blocks:
        for delta, _, _ in pairs:
            add_vector(image(delta, labels), 0, basis)
    return image(base, labels), [v for v, _ in basis.values()]


def solve(n, clauses, labels, target):
    """SAT plus assignment, UNSAT by hull, or UNKNOWN on a stalled quotient."""
    if len(labels) != n or any(type(v) is not int or v < 0 for v in labels) or type(target) is not int or target < 0:
        raise ValueError("expected nonnegative binary label masks")
    prepared = prepare(n, clauses)
    if prepared is None:
        return "UNSAT", None
    base, blocks = prepared
    needed = target ^ image(base, labels)
    total = {}
    for _, pairs in blocks:
        for delta, _, _ in pairs:
            add_vector(image(delta, labels), 0, total)
    if reduce_vector(needed, total)[0]:
        return "UNSAT", None
    realized = {}
    replacements = []
    remaining = list(blocks)
    while True:
        for j, (mask, pairs) in enumerate(remaining):
            residues = {reduce_vector(image(delta, labels), realized)[0]
                        for delta, _, _ in pairs} - {0}
            if len(residues) > 1:
                continue
            if residues:
                direction = next(iter(residues))
                for _, a, b in pairs:
                    for choice in (a,b):
                        changes = (base & mask) ^ choice
                        gain = image(changes, labels)
                        if reduce_vector(gain, realized)[0] == direction:
                            add_vector(gain, 1 << len(replacements), realized)
                            replacements.append(changes)
                            break
                    else:
                        continue
                    break
                else:
                    raise AssertionError("missing parity witness")
            remaining.pop(j)
            break
        else:
            break
    residual, selection = reduce_vector(needed, realized)
    if residual:
        return "UNKNOWN", None
    for j, changes in enumerate(replacements):
        if selection >> j & 1:
            base ^= changes
    return "SAT", base
