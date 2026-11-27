"""Polynomial-space sparse-prefix search for an even-degree self-adjoint drift."""
from itertools import combinations
from additive_safe_slope import _safe
from additive_slope_prefix import dickson
from half_line_carry_moments import HalfLineMoments
from kernel_half_line import selected_line
from product_slack import linearized
from quadratic_target import apply_basis
from selfadjoint_coset_sampler import subfield_basis
from sparse_line_prefix import dual_basis


def elementary(f, weights):
    values = [1] + [0]*len(weights)
    for j,w in enumerate(weights):
        for n in range(j+1,0,-1):
            values[n] ^= f.mul(values[n-1],w)
    return values


def coefficient(f, factors, a, residue):
    """Coefficient modulo T^(2^a−1)−1 of ∏(c_j+Tr_L(α_j T))."""
    h = len(factors)
    residue %= (1 << a)-1
    total = 0
    for subset in range(1 << h):
        chosen = [factors[j] for j in range(h) if subset >> j & 1]
        constants = elementary(f,[c for c,_ in chosen])
        weights = [w for _,w in chosen]
        terms = []
        for _ in range(a):
            terms.append([(n,c) for n,c in enumerate(elementary(f,weights)) if c])
            weights = [f.mul(w,w) for w in weights]
        for start in range(h+1):
            states = {(start,n):c for n,c in enumerate(constants) if c}
            for i, choices in enumerate(terms):
                bit = (residue >> i) & 1
                nxt = {}
                for (carry,used), val in states.items():
                    for n,c in choices:
                        diff = carry+n-bit
                        if used+n <= h and diff >= 0 and not diff % 2:
                            key = diff//2, used+n
                            nxt[key] = nxt.get(key,0) ^ f.mul(val,c)
                states = {key:v for key,v in nxt.items() if v}
            total ^= states.get((start,h),0)
    return total


def find_columns(f, columns, depth=None):
    center, scale = selected_line(f,columns)
    if scale is None:
        return center
    a = f.m//2
    h = 3*a//25 if depth is None else depth
    if not isinstance(h,int) or not 0 <= h <= a:
        raise ValueError("invalid prefix depth")
    basis = subfield_basis(f)
    dual = dual_basis(f,basis)
    coeffs = list(linearized(f,columns))
    coeffs[0] ^= center
    moments = HalfLineMoments(f,dickson(f,coeffs),scale)
    factors = []
    chosen = 0
    for i in range(h):
        factors.append((1,dual[i]))
        parity = 0
        for k in range(min(i+1,a-1)+1):
            for slots in combinations(range(a),k):
                r = sum(1<<j for j in slots)
                c = coefficient(f,factors,a,r)
                if c:
                    parity ^= f.mul(c,moments.moment(r) if r else 1)
        if parity == 0:
            factors[-1] = (0,dual[i])
            chosen |= 1 << i
        elif parity != 1:
            raise ArithmeticError("nonbinary prefix parity")
    for suffix in range(1 << (a-h)):
        t = apply_basis(basis,chosen | suffix<<h)
        slope = center ^ f.mul(scale,t)
        if _safe(f,columns,slope):
            return slope
    raise ArithmeticError("odd prefix had no original witness")
