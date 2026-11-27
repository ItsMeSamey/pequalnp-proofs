"""Uniform deterministic safe-slope search by parity on binary prefixes."""
from additive_safe_slope import _columns, _coefficients, _safe
from product_network_inequality import trace_dual


def dickson(field,coefficients):
    """D maps (x,x²,...) to (A(x),A(x)²,...)."""
    row=list(_coefficients(field,coefficients))
    rows=[]
    for _ in range(field.m):
        rows.append(row)
        row=[field.mul(v,v) for v in row[-1:]+row[:-1]]
    return rows


def _det(field,a):
    value=1
    for j in range(len(a)):
        pivot=next((i for i in range(j,len(a)) if a[i][j]),None)
        if pivot is None: return 0
        a[j],a[pivot]=a[pivot],a[j]
        p=a[j][j]
        value=field.mul(value,p)
        inv=field.inverse(p)
        for i in range(j+1,len(a)):
            c=field.mul(a[i][j],inv)
            if c:
                for k in range(j+1,len(a)): a[i][k] ^= field.mul(c,a[j][k])
    return value


def dickson_moment(field,D,t):
    if type(t) is not int or t<0: raise ValueError("invalid exponent")
    if not t: return 1
    r=t%(field.size-1)
    if not r: return _det(field,[row[:] for row in D])^1
    ids=[j for j in range(field.m) if r>>j&1]
    return _det(field,[[D[i][j] for j in ids] for i in ids])


def _product(field,poly,factor):
    N=field.size-1
    out={}
    for a,c in poly.items():
        for b,d in factor.items():
            exponent=a+b
            if exponent: exponent=1+(exponent-1)%N
            out[exponent]=out.get(exponent,0)^field.mul(c,d)
    return {t:v for t,v in out.items() if v}


def find(field,coefficients,*,prefix_bits=None):
    """Use floor(11m/50) low bits by default; prefix_bits overrides for controls."""
    coeffs=_coefficients(field,coefficients)
    m=field.m
    h=11*m//50 if prefix_bits is None else prefix_bits
    if type(h) is not int or not 0<=h<=m:
        raise ValueError("invalid prefix length")
    D=dickson(field,coeffs)
    poly={0:1}
    prefix=0
    moments={0:1}
    for k,alpha in enumerate(trace_dual(field)[:h]):
        # Trace(alpha*s) is binary coordinate k. 1+trace indicates bit zero.
        factor={0:1}
        for j in range(m):
            factor[1<<j]=alpha
            alpha=field.mul(alpha,alpha)
        zero=_product(field,poly,factor)
        parity=0
        for t,c in zero.items():
            if t not in moments: moments[t]=dickson_moment(field,D,t)
            parity ^= field.mul(c,moments[t])
        if parity==1:
            poly=zero
        elif parity==0:
            # The indicator for the other child is the parent plus the zero child.
            prefix |= 1<<k
            for t,c in zero.items():
                poly[t]=poly.get(t,0)^c
            poly={t:v for t,v in poly.items() if v}
        else:
            raise ArithmeticError("binary indicator sum outside prime field")
    cols=_columns(field,coeffs)
    for suffix in range(1<<(m-h)):
        s=prefix | (suffix<<h)
        if _safe(field,cols,s): return s
    raise ArithmeticError("odd prefix contained no safe slope")
