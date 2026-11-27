"""Decide simultaneous sparse inequations on a fixed binary-field torus."""
from dataclasses import dataclass
from math import gcd, prod
from sympy import Matrix, eye
from sympy.matrices.normalforms import hermite_normal_form
from affine_binomial import power
from binomial_inequation import primitive_combination, ratio
from field_plane_root import rational_roots
from torus_factor_blocks import independent_blocks


@dataclass(frozen=True)
class Decision:
    status: str
    overlap: int | None
    peak_states: int = 0


def _relations(order, n, rows):
    h = len(rows)
    matrix = Matrix(h, n, [v % order for row in rows for v in row])
    basis = hermite_normal_form(matrix.row_join(order * eye(h)), D=order**h)
    return [[int(v) % order for v in row] for row in (order * basis.inv()).tolist()]


def _monomial(field, values, exponents):
    acc = 1
    order = field.size - 1
    for x, k in zip(values, exponents):
        if k % order:
            acc = field.mul(acc, power(field, x, k % order))
    return acc


def _values(field, n, rows, constants, new, limit):
    order = field.size - 1
    relations = _relations(order, n, [*rows, new])
    coeff = [row[-1] for row in relations]
    g = gcd(order, *coeff)
    if g > limit:
        raise ArithmeticError("local degree exceeds overlap bound")
    bezout = primitive_combination([s // g for s in coeff], order // g)
    targets = [_monomial(field, constants, [-v for v in row[:-1]]) for row in relations]
    d = _monomial(field, targets, bezout)
    return [d] if g == 1 else rational_roots(field, (d,) + (0,) * (g-1) + (1,))


def _nonzero(field, rows, constants, terms):
    # Distinct characters on the homogeneous kernel are linearly independent.
    classes = []
    for c, ex in terms:
        for i, (anchor, old) in enumerate(classes):
            factor = ratio(field, rows, constants, tuple(a-b for a,b in zip(ex,anchor)))
            if factor is not None:
                classes[i] = anchor, old ^ field.mul(c, factor)
                break
        else:
            classes.append((ex, c))
    return any(c for _, c in classes)


def decide(field, n, rows, constants, polynomials, *, max_overlap=256):
    """Rows (signed exponent vectors) impose x^row=c; each term is (c,exponents)."""
    order = field.size - 1
    if n < 0 or max_overlap < 0:
        raise ValueError("invalid dimension or overlap limit")

    def row(ex):
        ex = tuple(ex)
        if len(ex) != n or any(not isinstance(v, int) for v in ex):
            raise ValueError("invalid exponent vector")
        return tuple(v % order for v in ex)

    rows = [row(ex) for ex in rows]
    constants = list(constants)
    if len(rows) != len(constants) or any(not 0 < c < field.size for c in constants):
        raise ValueError("invalid torus constants")
    terms_list = []
    for polynomial in polynomials:
        combined = {}
        for c, ex in polynomial:
            if not 0 <= c < field.size:
                raise ValueError("invalid coefficient")
            ex = row(ex)
            combined[ex] = combined.get(ex, 0) ^ c
        terms_list.append([(c,ex) for ex,c in combined.items() if c])
    if any(_monomial(field, constants, rel) != 1 for rel in _relations(order,n,rows)):
        return Decision("UNSAT", None)
    if any(not terms for terms in terms_list):
        return Decision("UNSAT", None)
    groups = []
    for terms in terms_list:
        anchor = terms[0][1]
        groups.append([tuple((a-b) % order for a,b in zip(ex,anchor)) for _,ex in terms[1:]])
    _, joint, marginal = independent_blocks(order,n,rows,groups)
    overlap = prod(marginal) // joint
    if overlap > max_overlap:
        return Decision("UNKNOWN", overlap)
    relations = _relations(order,n,rows + [r for block in groups for r in block])
    h = len(relations)
    goal = tuple(_monomial(field,constants,[-v for v in rel[:len(rows)]]) for rel in relations)
    partial = {(1,) * h}
    peak = 1
    start = len(rows)
    for terms, block in zip(terms_list,groups):
        signatures = [(tuple(), [])]
        pins = []
        for rel in relations:
            new = tuple(sum(s * br[j] for s,br in zip(rel[start:start+len(block)],block)) % order
                        for j in range(n))
            if not any(new):
                signatures = [(sig+(1,), vals) for sig,vals in signatures]
                continue
            next_signatures = []
            for sig, vals in signatures:
                for z in _values(field,n,rows+pins,constants+vals,new,overlap):
                    next_signatures.append((sig+(z,), vals+[z]))
            signatures = next_signatures
            pins.append(new)
        allowed = [sig for sig,vals in signatures if _nonzero(field,rows+pins,constants+vals,terms)]
        partial = {tuple(field.mul(a,b) for a,b in zip(prev,sig)) for prev in partial for sig in allowed}
        peak = max(peak,len(signatures),len(partial))
        if peak > overlap:
            raise ArithmeticError("signature table exceeds overlap")
        if not partial:
            return Decision("UNSAT", overlap, peak)
        start += len(block)
    return Decision("SAT" if goal in partial else "UNSAT", overlap, peak)
