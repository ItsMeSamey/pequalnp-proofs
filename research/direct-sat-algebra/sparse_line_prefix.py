"""Deterministic sub-square-root safe slope in every even binary degree, self-adjoint drift."""
from additive_safe_slope import _safe
from additive_slope_prefix import dickson
from commuting_spread import inverse_columns
from kernel_half_line import selected_line
from product_slack import linearized
from quadratic_target import apply_basis
from selfadjoint_coset_sampler import subfield_basis


def dual_basis(f, basis):
    def trace(x):
        total = 0
        for _ in basis:
            total ^= x
            x = f.mul(x,x)
        if total not in (0,1):
            raise ArithmeticError("input basis outside half-field")
        return total
    gram = [sum(trace(f.mul(x,y)) << j for j,y in enumerate(basis)) for x in basis]
    return [apply_basis(basis,v) for v in inverse_columns(gram)]


def find_columns(f, columns, depth=None):
    from half_line_carry_moments import HalfLineMoments
    center, scale = selected_line(f, columns)
    if scale is None:
        return center
    a = f.m//2
    h = 3*a//25 if depth is None else depth
    if not isinstance(h,int) or not 0 <= h <= a:
        raise ValueError("invalid prefix depth")
    basis = subfield_basis(f)
    coeffs = list(linearized(f,columns))
    coeffs[0] ^= center
    moments = HalfLineMoments(f,dickson(f,coeffs),scale)
    cache = {0:1}
    indicator = {0:1}
    chosen = 0
    modulus = (1 << a)-1
    for i, alpha in enumerate(dual_basis(f,basis)[:h]):
        zero = dict(indicator)
        for j in range(a):
            for r, c in indicator.items():
                pos = (r+(1<<j)) % modulus
                zero[pos] = zero.get(pos,0) ^ f.mul(c,alpha)
            alpha = f.mul(alpha,alpha)
        zero = {r:c for r,c in zero.items() if c}
        parity = 0
        for r,c in zero.items():
            if r not in cache:
                cache[r] = moments.moment(r)
            parity ^= f.mul(c,cache[r])
        if parity == 0:
            chosen |= 1 << i
            for r,c in indicator.items():
                zero[r] = zero.get(r,0)^c
        elif parity != 1:
            raise ArithmeticError("nonbinary prefix parity")
        indicator = {r:c for r,c in zero.items() if c}
    for suffix in range(1 << (a-h)):
        t = apply_basis(basis,chosen | (suffix<<h))
        s = center ^ f.mul(scale,t)
        if _safe(f,columns,s):
            return s
    raise ArithmeticError("odd prefix had no original witness")
