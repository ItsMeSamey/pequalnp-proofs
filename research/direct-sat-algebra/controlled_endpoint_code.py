"""Recognize affine endpoint classes and count signed two-spin models exactly."""
from dataclasses import dataclass
from itertools import combinations
from math import prod

from controlled_witness_radius import column_basis, row_equations
from quadratic_target import affine_domain, apply_basis, parity, reduce_vector


@dataclass
class Result:
    status: str
    count: int | None
    witness: tuple | None
    codimension: int
    width: int
    classes: int
    lift_dimension: int


def elimination_order(size, scopes):
    neighbors = [set() for _ in range(size)]
    for scope in scopes:
        for a, b in combinations(scope, 2):
            neighbors[a].add(b)
            neighbors[b].add(a)
    remaining = set(range(size))
    order = []
    width = 0
    while remaining:
        vertex = min(remaining, key=lambda v: (len(neighbors[v]), v))
        adjacent = neighbors[vertex]
        width = max(width, len(adjacent))
        for v in adjacent:
            neighbors[v].remove(vertex)
            neighbors[v].update(adjacent - {v})
        remaining.remove(vertex)
        order.append(vertex)
    return order, width


def eliminate(factors, order):
    factors = list(factors)
    for v in order:
        live = [(s, t) for s, t in factors if v in s]
        factors = [(s, t) for s, t in factors if v not in s]
        scope = tuple(sorted({j for s, _ in live for j in s} - {v}))
        axes = (v,) + scope
        indexed = [([axes.index(j) for j in s], t) for s, t in live]
        out = [0] * (1 << len(scope))
        for mask in range(2 << len(scope)):
            out[mask >> 1] += prod(t[sum(((mask >> j) & 1) << i
                                          for i, j in enumerate(pos))]
                                   for pos, t in indexed)
        factors.append((scope, out))
    return prod(t[0] for _, t in factors)


def solve(m, A, b, U, activators, *, max_codimension=None, max_width=None):
    """Packed original controlled pencil, witness (control bits x, data bits y)."""
    A, U, activators = tuple(A), tuple(U), tuple(activators)
    n, k = len(A), len(U)
    if (m < 0 or len(activators) != k or any(not 0 <= v < 1 << m for v in (*A, b, *U))
        or any(not 0 <= f < 1 << n or c not in (0, 1) for f, c in activators)
        or any(c is not None and c < 0 for c in (max_width, max_codimension))):
        raise ValueError("invalid pencil or cap")
    data = [(a << k) | sum(((f >> j) & 1) << i for i, (f, _) in enumerate(activators))
            for j, a in enumerate(A)]
    shift = (b << k) | sum(c << i for i, (_, c) in enumerate(activators))
    basis = column_basis(data)
    lift = n - len(basis)
    def residue(v):
        return reduce_vector(v, basis)[0]
    cols = [residue(1 << i) for i in range(k)] + [residue(u << k) for u in U]
    flat = affine_domain(2*k, row_equations(cols, residue(shift), k+m))
    if flat is None:
        return Result("UNSAT", 0, None, 0, 0, 0, lift)
    offset, dirs, _ = flat
    types = {}
    endpoints = []
    factors = []
    for i in range(k):
        pair = []
        for mask in (1 << (k+i), (1 << (k+i)) | (1 << i)):
            form = sum(parity(d & mask) << j for j, d in enumerate(dirs))
            label = types.setdefault(form, len(types)) if form else None
            pair.append((label, parity(offset & mask)))
        endpoints.append(pair)
        scope = tuple(sorted({v for v, _ in pair if v is not None}))
        table = []
        for bits in range(1 << len(scope)):
            a, d = [c ^ (0 if v is None else (bits >> scope.index(v)) & 1) for v, c in pair]
            table.append(2 - a - d)
        factors.append((scope, table))
    size = len(types)
    # z contains homogeneous representatives; endpoint offsets stay in the factors.
    relations = affine_domain(size, [(row, 0) for row, _ in
                              row_equations(list(types), 0, len(dirs))])[1]
    h = len(relations)
    order, width = elimination_order(size, [s for s, _ in factors])
    def result(status, count=None, witness=None):
        return Result(status, count, witness, h, width, size, lift)
    if ((max_width is not None and width > max_width) or
        (max_codimension is not None and h > max_codimension)):
        return result("UNKNOWN")
    def count(pins):
        total = 0
        for mask in range(1 << h):
            char = apply_basis(relations, mask)
            unary = []
            for j in order:
                sign = -1 if char >> j & 1 else 1
                pin = pins.get(j)
                unary.append(((j,), (int(pin != 1), sign * int(pin != 0))))
            total += eliminate(factors + unary, order)
        answer, rem = divmod(total, 1 << h)
        if rem or answer < 0:
            raise ArithmeticError("invalid projected count")
        return answer
    value = count({})
    if not value:
        return result("UNSAT", 0)
    pins = {}
    for j in order:
        pins[j] = 0
        if not count(pins):
            pins[j] = 1
    q = w = 0
    for i, pair in enumerate(endpoints):
        a, d = [c ^ (0 if v is None else pins[v]) for v, c in pair]
        w |= a << i
        q |= (a ^ d) << i
    target = (q | (apply_basis(U, w) << k)) ^ shift
    y = affine_domain(n, row_equations(data, target, k+m))[0]
    return result("SAT", value << lift, (w, y))
