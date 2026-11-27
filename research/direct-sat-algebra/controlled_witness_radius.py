"""Witness search for an aligned binary control pencil presented as packed columns.

For n data bits y and k independent control bits x, solve
sum_i x_i u_i (v_i.y + c_i) = A y + b, on a supplied affine data flat.
A and U are sequences of m-bit columns. Activators are (n-bit mask, bit).
A None result certifies divisibility of the normalized count, not necessarily UNSAT.
"""

from itertools import combinations

from quadratic_target import affine_domain, apply_basis, insert, parity, reduce_vector


def column_basis(columns):
    """Return triangular rows with coordinates in the greedy independent basis."""
    rows = {}
    for value in columns:
        insert(value, 1 << len(rows), rows)
    return rows


def row_equations(columns, target, width):
    """Transpose packed columns to scalar affine equations."""
    return [(sum(((col >> j) & 1) << i for i, col in enumerate(columns)),
             (target >> j) & 1) for j in range(width)]


class ProjectedOracle:
    """Exact count of (data, remaining controls), after eliminating a known active span."""

    def __init__(self, m, A, b, remaining, activators, active_basis, equations):
        self.n = len(A)
        self.activators = tuple(activators)
        self.equations = list(equations)
        quotient = [reduce_vector(u, active_basis)[0] for u in remaining]
        basis = column_basis(quotient)
        self.rank = len(basis)
        self.u = [reduce_vector(u, basis)[1] for u in quotient]
        images = []
        for target in (*A, b):
            quotient_target, _ = reduce_vector(target, active_basis)
            images.append(reduce_vector(quotient_target, basis))
        self.A = [coords for _, coords in images[:-1]]
        self.b = images[-1][1]
        self.equations += row_equations([res for res, _ in images[:-1]], images[-1][0], m)

    def count(self, pins=()):
        base = self.equations + list(pins)
        if affine_domain(self.n, base) is None:
            return 0
        total = 0
        for h in range(1 << self.rank):
            conditions = [q for q, u in zip(self.activators, self.u) if parity(h & u)]
            flat = affine_domain(self.n, base + conditions)
            if flat is None:
                continue
            origin, directions, _ = flat
            sign_mask = sum(parity(h & col) << i for i, col in enumerate(self.A))
            if any(parity(sign_mask & d) for d in directions):
                continue
            sign = parity(h & self.b) ^ parity(sign_mask & origin)
            contribution = 1 << len(directions)
            total += -contribution if sign else contribution
        return total << (len(self.u) - self.rank)

    def witness_y(self):
        if not self.count():
            return None
        pins = []
        value = 0
        for i in range(self.n):
            bit = 1 << i
            chosen = int(self.count(pins + [(bit, 0)]) == 0)
            pins.append((bit, chosen))
            value |= chosen << i
        return value


def search(m, A, b, U, activators, precision, selected=None, equations=()):
    """Return (x,y) or None. selected may be any independent set of column indices."""
    A, U, activators, equations = tuple(A), tuple(U), tuple(activators), tuple(equations)
    n, k = len(A), len(U)
    if m < 0 or precision < 1 or len(activators) != k:
        raise ValueError("invalid dimensions or precision")
    if any(not 0 <= col < 1 << m for col in (*A, b, *U)):
        raise ValueError("output column exceeds dimension")
    if any(not 0 <= mask < 1 << n or bit not in (0, 1)
           for mask, bit in activators + equations):
        raise ValueError("invalid data form")
    if selected is None:
        greedy = {}
        selected = [i for i,u in enumerate(U) if insert(u,0,greedy)]
    selected = tuple(selected)
    selected_set = set(selected)
    if (any(i < 0 or i >= k for i in selected) or
            len(column_basis(U[i] for i in selected)) != len(selected)):
        raise ValueError("selected indices must be independent")
    remainder = [i for i in range(k) if i not in selected_set]
    T = len(column_basis(U[i] for i in remainder))
    overlap = len(selected) + T - len(column_basis(U))
    radius = min(len(selected), overlap + precision - 1)
    for j in range(radius + 1):
        for missing in combinations(selected, j):
            inactive = set(missing)
            active = [i for i in selected if i not in inactive]
            pattern = [(activators[i][0], activators[i][1] ^ int(i not in inactive))
                       for i in selected]
            oracle = ProjectedOracle(m, A, b, [U[i] for i in remainder],
                                     [activators[i] for i in remainder],
                                     column_basis(U[i] for i in active), equations + tuple(pattern))
            y = oracle.witness_y()
            if y is None:
                continue
            rows = {}
            for i, (mask, constant) in enumerate(activators):
                if parity(mask & y) ^ constant:
                    insert(U[i], 1 << i, rows)
            residual, x = reduce_vector(apply_basis(A, y) ^ b, rows)
            if residual:
                raise AssertionError("projected solution did not lift")
            return x, y
    return None
