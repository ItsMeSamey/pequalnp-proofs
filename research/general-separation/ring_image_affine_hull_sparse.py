"""Sparse affine-hull closure and groupwise 2-CNF testing in a recovered chart."""
from itertools import combinations
from read_two_ring_image import recover
from ring_image_coordinate_2sat import _insert, _reduce, _lift, _two_sat, coordinate_axes


def _parity(mask):
    return mask.bit_count() & 1


class Span:
    """Express a vector as a mask of independent supplied rows."""
    def __init__(self):
        self.rows = {}
        self.axes = []

    def decompose(self, v):
        coeff = 0
        for pivot in sorted(self.rows, reverse=True):
            if v >> pivot & 1:
                row, code = self.rows[pivot]
                v ^= row
                coeff ^= code
        return v, coeff

    def append(self, v):
        rem, code = self.decompose(v)
        if not rem:
            return False
        self.rows[rem.bit_length()-1] = rem, code ^ (1 << len(self.axes))
        self.axes.append(v)
        return True


def _combine(axes, code):
    result = 0
    while code:
        bit = code & -code
        result ^= axes[bit.bit_length()-1]
        code ^= bit
    return result


def _project(scope, forbidden, eq):
    # On the current affine space x_j = offset_j + row_j * free coordinates.
    local = [_reduce(1 << i, 0, eq) for i in scope]
    span = Span()
    selected = []
    for j, (row, _) in enumerate(local):
        if span.append(row):
            selected.append(j)
    codes = [span.decompose(row)[1] for row,_ in local]
    offset = sum(c << i for i,(_,c) in enumerate(local))
    reachable = set()
    for f in forbidden:
        raw = f ^ offset
        t = sum(((raw >> j) & 1) << i for i,j in enumerate(selected))
        if all(_parity(code & t) == ((raw >> j) & 1) for j,code in enumerate(codes)):
            reachable.add(t)
    return span, reachable


def _flat(words, dim):
    anchor = next(iter(words))
    rows = {}
    for w in words:
        _insert(w ^ anchor, 0, rows)
    normal = []
    for j in range(dim):
        if j not in rows:
            axis = _lift(rows, 1 << j)
            normal.append((axis, _parity(axis & anchor)))
    return normal, len(words) == 1 << len(rows)


def _closure(groups):
    eq = {}
    while True:
        projected = []
        for scope, forbidden in groups.items():
            span, words = _project(scope, forbidden, eq)
            size = 1 << len(span.axes)
            if len(words) == size:
                return None, None
            if not words:
                continue
            projected.append((span, words))
            if 2 * len(words) < size:
                continue
            allowed = set(range(size)) - words
            normals, _ = _flat(allowed, len(span.axes))
            if normals:
                for normal, bit in normals:
                    if not _insert(_combine(span.axes, normal), bit, eq):
                        raise AssertionError("inconsistent nonempty affine hull")
                break  # All local projections now need refreshing.
        else:
            return eq, projected


def _binary_cover(span, words, axes):
    """Test all unary/binary cylinders in this fixed full chart."""
    projected_axes = [span.decompose(a) for a in axes]
    covered = set()
    constraints = []
    for width in (1,2):
        for ids in combinations(range(len(axes)), width):
            # Linear combinations of chosen axes lying in row(C) give
            # precisely the equations of the projected cylinder.
            equations = []
            for subset in range(1,1 << width):
                residual = code = 0
                for j, i in enumerate(ids):
                    if subset >> j & 1:
                        rem, combination = projected_axes[i]
                        residual ^= rem
                        code ^= combination
                if not residual:
                    equations.append((subset, code))
            rank = len(equations).bit_length()  # counts are 0, 1, or 3
            target = 1 << (len(span.axes)-rank)
            if target > len(words):
                continue
            for pattern in range(1 << width):
                hits = {t for t in words if all(_parity(t & code) == _parity(pattern & s)
                                                for s,code in equations)}
                if len(hits) == target:
                    covered.update(hits)
                    constraints.append([(axes[i], (pattern >> j) & 1) for j,i in enumerate(ids)])
    return constraints if covered == words else None


def solve_source_sparse(arity, signed_clauses):
    """Return sorted true original variable IDs. All other IDs default to zero."""
    if type(arity) is not int or arity < 0:
        raise ValueError("invalid arity")
    source = tuple(tuple(row) for row in signed_clauses)
    if any(type(x) is not int or not 1 <= abs(x) <= arity for row in source for x in row):
        raise ValueError("invalid signed literal")
    used = sorted({abs(x) for row in source for x in row})
    index = {v:i for i,v in enumerate(used)}
    groups = {}
    for row in source:
        lits = set(row)
        if any(-x in lits for x in lits):
            continue
        names = sorted(map(abs, lits))
        scope = tuple(index[x] for x in names)
        groups.setdefault(scope,set()).add(sum(1 << j for j,x in enumerate(names) if -x in lits))
    eq, projected = _closure(groups)
    if eq is None:
        return dict(status="zero")
    flat_tests = []
    other = []
    for span, words in projected:
        normals, flat = _flat(words, len(span.axes))
        if flat and len(normals) <= 2:
            flat_tests.append([(_combine(span.axes, a), b) for a,b in normals])
        else:
            other.append((span, words))
    axes = coordinate_axes(flat_tests)
    if axes is None:
        return dict(status="unknown", reason="incompatible_axes")
    basis = Span()
    for a in axes:
        basis.append(a)
    for i in range(len(used)):
        if i not in eq:
            basis.append(1 << i)
    tests = list(flat_tests)
    for span, words in other:
        cover = _binary_cover(span, words, basis.axes)
        if cover is None:
            return dict(status="unknown", reason="fixed_chart_cover")
        tests.extend(cover)
    bits = _two_sat(basis.axes, tests)
    if bits is None:
        return dict(status="zero")
    for a,b in zip(basis.axes,bits):
        if not _insert(a,b,eq):
            raise AssertionError("inconsistent chart lift")
    word = _lift(eq)
    selected = {v for i,v in enumerate(used) if word >> i & 1}
    if not all(any((abs(x) in selected) == (x > 0) for x in row) for row in source):
        raise AssertionError("invalid source witness")
    return dict(status="nonzero", true_ids=tuple(sorted(selected)))


def solve_source(arity, signed_clauses):
    """Dense compatibility endpoint; materializing a witness costs Omega(arity)."""
    result = solve_source_sparse(arity, signed_clauses)
    if result["status"] != "nonzero":
        return result
    true_ids = set(result["true_ids"])
    return dict(status="nonzero", assignment=tuple(int(x in true_ids) for x in range(1,arity+1)))


def solve_sparse(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    return dict(status="off_image") if source is None else solve_source_sparse(*source)


def solve(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    return dict(status="off_image") if source is None else solve_source(*source)
