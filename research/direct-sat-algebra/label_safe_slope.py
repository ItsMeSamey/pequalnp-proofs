"""Unconditional square-root-time safe slope in a supplied binary field."""
from additive_safe_slope import _coefficients, _columns, _safe
from additive_slope_prefix import dickson
from label_subset_ring import LabelRing
from product_network_inequality import trace_dual
from product_slack import linearized


def expectation(f, D, factors):
    """Parity of safe s satisfying c+Tr(alpha*s)=1 for every (c,alpha)."""
    h = len(factors)
    if not h:
        return 1
    ring = LabelRing(f,h)
    B = [ring.zero]*f.m
    const = ring.one
    for j,(c,alpha) in enumerate(factors):
        if c not in (0,1):
            raise ValueError("nonbinary affine offset")
        monomial = [0]*(1<<h)
        if c:
            monomial[1<<j] = 1
            const = ring.mul(const,ring.add(ring.one,monomial))
        for i in range(f.m):
            monomial[1<<j] = alpha
            carry = tuple(monomial)
            pos = i
            while any(carry):
                old = B[pos]
                B[pos] = ring.add(old,carry)
                carry = ring.mul(old,carry)
                pos = (pos+1)%f.m
            alpha = f.mul(alpha,alpha)
    matrix = [[tuple(f.mul(x,D[i][j]) for x in B[i]) for j in range(f.m)] for i in range(f.m)]
    for i in range(f.m):
        matrix[i][i] = ring.add(matrix[i][i],ring.one)
    det = ring.one
    for i in range(f.m):
        pivot = matrix[i][i]
        if pivot[0] != 1:
            raise ArithmeticError("nonunit pivot")
        det = ring.mul(det,pivot)
        for j in range(i+1,f.m):
            factor = ring.mul(matrix[j][i],pivot)
            for k in range(i+1,f.m):
                matrix[j][k] = ring.add(matrix[j][k],ring.mul(factor,matrix[i][k]))
    if h >= f.m:
        correction = ring.one
        for v in B:
            correction = ring.mul(correction,v)
        det = ring.add(det,correction)
    result = ring.mul(const,det)[-1]
    if result not in (0,1):
        raise ArithmeticError("nonbinary parity")
    return result


def find(f, coefficients, depth=None):
    a = _coefficients(f,coefficients)
    h = f.m//2 if depth is None else depth
    if type(h) != int or not 0 <= h <= f.m:
        raise ValueError("invalid depth")
    D = dickson(f,a)
    factors = []
    prefix = 0
    for i,alpha in enumerate(trace_dual(f)[:h]):
        factors.append((1,alpha))
        if not expectation(f,D,factors):
            factors[-1] = (0,alpha)
            prefix |= 1<<i
    cols = _columns(f,a)
    for suffix in range(1<<(f.m-h)):
        slope = prefix | (suffix<<h)
        if _safe(f,cols,slope):
            return slope
    raise ArithmeticError("no witness in odd prefix")


def find_columns(f, columns, depth=None):
    columns = tuple(columns)
    if len(columns)!=f.m or any(type(v)!=int or not 0<=v<f.size for v in columns):
        raise ValueError("invalid original columns")
    result = find(f,linearized(f,columns),depth)
    if not _safe(f,columns,result):
        raise ArithmeticError("original rank replay failed")
    return result
