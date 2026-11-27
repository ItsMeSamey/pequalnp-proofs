"""Stream the squarefree top-coefficient sieve using polynomial space."""
from additive_safe_slope import _coefficients, _columns, _safe
from additive_slope_prefix import dickson
from product_network_inequality import trace_dual
from product_slack import linearized


def _evaluate(f, D, factors, active):
    h = len(factors)
    zero = (0,) * (h+1)
    one = (1,) + zero[1:]

    def add(a,b):
        return tuple(x^y for x,y in zip(a,b))

    def mul(a,b):
        out = [0]*(h+1)
        for i,x in enumerate(a):
            if x:
                for j in range(h+1-i):
                    if b[j]:
                        out[i+j] ^= f.mul(x,b[j])
        return tuple(out)

    B = [zero]*f.m
    const = one
    for j,(c,alpha) in enumerate(factors):
        if not (active >> j)&1:
            continue
        if c:
            const = mul(const,(1,1)+zero[2:])
        for i in range(f.m):
            carry = (0,alpha)+zero[2:]
            pos = i
            # All B have zero constant coefficient; each carry raises degree.
            while any(carry):
                old = B[pos]
                B[pos] = add(old,carry)
                carry = mul(old,carry)
                pos = (pos+1)%f.m
            alpha = f.mul(alpha,alpha)
    M = [[tuple(f.mul(v,d) for v in B[i]) for d in row] for i,row in enumerate(D)]
    for i in range(f.m):
        M[i][i] = add(M[i][i],one)
    det = one
    for i in range(f.m):
        pivot = M[i][i]
        det = mul(det,pivot)
        for j in range(i+1,f.m):
            # This copies the multivariate circuit gate, even when pivot² != 1 here.
            factor = mul(M[j][i],pivot)
            for k in range(i+1,f.m):
                M[j][k] = add(M[j][k],mul(factor,M[i][k]))
    if h>=f.m:
        correction = one
        for v in B:
            correction = mul(correction,v)
        det = add(det,correction)
    return mul(const,det)[h]


def expectation(f,D,factors):
    """Parity of safe slopes satisfying all c+Tr(alpha*s)=1."""
    factors = tuple(factors)
    if any(c not in (0,1) or not 0<=alpha<f.size for c,alpha in factors):
        raise ValueError("invalid affine trace factor")
    if not factors:
        return 1
    total = 0
    for active in range(1<<len(factors)):
        total ^= _evaluate(f,D,factors,active)
    if total not in (0,1):
        raise ArithmeticError("nonbinary parity")
    return total


def find(f,coefficients,depth=None):
    a = _coefficients(f,coefficients)
    h = f.m//2 if depth is None else depth
    if type(h)!=int or not 0<=h<=f.m:
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
    for tail in range(1<<(f.m-h)):
        slope = prefix | (tail<<h)
        if _safe(f,cols,slope):
            return slope
    raise ArithmeticError("odd prefix yielded no safe slope")


def find_columns(f,columns,depth=None):
    columns = tuple(columns)
    if len(columns)!=f.m or any(type(v)!=int or not 0<=v<f.size for v in columns):
        raise ValueError("invalid original columns")
    result = find(f,linearized(f,columns),depth)
    if not _safe(f,columns,result):
        raise ArithmeticError("original rank replay failed")
    return result
