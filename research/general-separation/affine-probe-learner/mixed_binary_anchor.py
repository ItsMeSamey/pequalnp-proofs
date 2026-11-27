"""An original-coordinate anchor for simultaneous binary clauses and XOR rows.

Literal (i,b) requires coordinate i (zero is most significant) to equal b.
An equation (mask,b) requires parity(mask & packed_assignment) == b.
"""
from dataclasses import dataclass
from itertools import product

from affine_independence_portfolio import basis
from binary_fault_retraction import Gamma
from quadratic_polar_online import _space


@dataclass(frozen=True)
class AnchorResult:
    witness: int | None
    p: int
    q: int
    route: str
    fibers: int


def _indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def _parity(mask):
    return mask.bit_count() & 1


def _clauses(n, clauses):
    result = []
    for clause in clauses:
        literals = set()
        for i, b in clause:
            if type(i) is not int or not 0 <= i < n or type(b) is not int or b not in (0, 1):
                raise ValueError('invalid literal')
            literals.add((i, b))
        if len(literals) > 2:
            raise ValueError('clause width exceeds two')
        if any((i, b ^ 1) in literals for i, b in literals):
            continue
        result.append(tuple(sorted(literals)))
    return tuple(result)


def _project(rows, active):
    """Eliminate columns outside active before echelonizing the remaining checks."""
    eliminated = {}
    kept = []
    for mask, bit in rows:
        while mask & ~active:
            pivot = (mask & ~active).bit_length()-1
            if pivot not in eliminated:
                eliminated[pivot] = mask, bit
                break
            other, rhs = eliminated[pivot]
            mask ^= other
            bit ^= rhs
        else:
            kept.append((mask << 1) | bit)
    return tuple((v >> 1, v & 1) for v in basis(kept))


def _coordinate_plan(projected):
    selected = 0
    for mask, _ in projected:
        residual = mask & ~selected
        while residual.bit_count() > 2:
            bit = residual & -residual
            selected |= bit
            residual ^= bit
    return tuple(_indices(selected))


def _coordinate_fiber(n, clauses, rows, projected, active, selected, answer):
    gamma = Gamma(n)
    for c in clauses:
        gamma.add_cube((i, b ^ 1) for i, b in c)
    fixed = sum(1 << pos for pos in selected)
    values = sum(((answer >> i) & 1) << pos for i, pos in enumerate(selected))
    for pos in selected:
        gamma.add_cube(((n-pos-1, 1 ^ ((values >> pos) & 1)),))
    for mask, rhs in projected:
        rhs ^= _parity(mask & values)
        remaining = tuple(_indices(mask & ~fixed))
        for bits in product((0, 1), repeat=len(remaining)):
            if sum(bits) % 2 != rhs:
                gamma.add_cube((n-pos-1, b) for pos, b in zip(remaining, bits))
    partial = gamma.model()
    if partial is None:
        return None
    pins = [(1 << pos, (partial >> pos) & 1) for pos in _indices(active)]
    completion = _space(n, (*rows, *pins))
    if completion is None:
        raise AssertionError('projected model has no affine lift')
    return completion[0]


def _affine_plan(n, clauses, origin, directions):
    chart = []
    cuts = ()
    for clause in clauses:
        forms = set()
        satisfied = False
        for i, bit in clause:
            pos = n-i-1
            rhs = bit ^ ((origin >> pos) & 1)
            normal = sum(((v >> pos) & 1) << j for j, v in enumerate(directions))
            if normal:
                forms.add((normal, rhs))
            elif not rhs:
                satisfied = True
        if satisfied or any((a, b ^ 1) in forms for a, b in forms):
            continue
        terms = tuple(sorted(forms))
        chart.append(terms)
        if len(terms) == 2 and all(len(basis((*cuts, a))) > len(cuts) for a, _ in terms):
            cuts = basis((*cuts, terms[0][0]))
    return chart, cuts


def _affine_fiber(origin, directions, chart, cuts, answer):
    dim = len(directions)
    equations = [(a, (answer >> i) & 1) for i, a in enumerate(cuts)]
    center, free, _ = _space(dim, equations)
    for terms in chart:
        residual = []
        for a, b in terms:
            if any(_parity(a & v) for v in free):
                residual.append((a, b))
            elif _parity(a & center) == b:
                break
        else:
            if not residual:
                return None
            if len(residual) != 1:
                raise AssertionError('missing affine cut')
            equations.append(residual[0])
    completion = _space(dim, equations)
    if completion is None:
        return None
    point = origin
    for i in _indices(completion[0]):
        point ^= directions[i]
    return point


def solve(n, clauses, rows):
    """Return an original assignment or certify UNSAT by exhausting the chosen fibers."""
    if type(n) is not int or n < 0:
        raise ValueError('invalid dimension')
    clauses = _clauses(n, clauses)
    rows = tuple((a, b) for a, b in rows)
    for a, b in rows:
        if type(a) is not int or a < 0 or a.bit_length() > n or type(b) is not int or b not in (0, 1):
            raise ValueError('invalid Gaussian equation')
    flat = _space(n, rows)
    if flat is None or () in clauses:
        return AnchorResult(None, 0, 0, 'inconsistent', 0)
    active = 0
    for clause in clauses:
        for i, _ in clause:
            active |= 1 << (n-i-1)
    projected = _project(rows, active)
    selected = _coordinate_plan(projected)
    origin, directions, _ = flat
    chart, cuts = _affine_plan(n, clauses, origin, directions)
    p, q = len(selected), len(cuts)
    route = 'coordinate' if p <= q else 'affine'
    for answer in range(1 << min(p, q)):
        if route == 'coordinate':
            point = _coordinate_fiber(n, clauses, rows, projected, active, selected, answer)
        else:
            point = _affine_fiber(origin, directions, chart, cuts, answer)
        if point is None:
            continue
        if not all(_parity(a & point) == b for a, b in rows):
            raise AssertionError('returned point violates XOR checks')
        if not all(any(((point >> (n-i-1)) & 1) == b for i, b in c) for c in clauses):
            raise AssertionError('returned point violates a binary clause')
        return AnchorResult(point, p, q, route, answer+1)
    return AnchorResult(None, p, q, route, 1 << min(p, q))
