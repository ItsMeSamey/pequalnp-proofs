"""Safe slope near any shifted Frobenius with verified binary rank-k error."""
from math import gcd
from additive_safe_slope import _safe
from affine_binomial import power
from deterministic_norm_lift import norm_preimage
from hidden_product_network import encoder
from punctured_chart_witness import power_chart
from quadratic_centroid import independent,zero_combinations
from quadratic_target import apply_basis
from shifted_frobenius_decode import fits


def _inputs(f,columns,k):
    cols=tuple(columns)
    if len(cols)!=f.m or any(type(y)!=int or not 0<=y<f.size for y in cols):
        raise ValueError("invalid raw columns")
    if type(k)!=int or k<0:raise ValueError("invalid rank radius")
    return cols


def _orbit(f,step,limit):
    x=1
    for _ in range(limit):
        yield x
        x=f.mul(x,step)
        if x==1:break


def _subfield(f,g):
    return zero_combinations([1<<i for i in range(f.m)],lambda x:x^power(f,x,1<<g))


def _norms(f,basis,decode,g,k,u):
    Q=1<<g
    if g<=k:
        for i in range(1,Q):yield apply_basis(basis,i)
        return
    bound=min(Q-1,2*(2*g+1)**(2*k))
    for i in range(1,min(u,Q-1)+1):
        for w in _orbit(f,decode(i),bound):
            if w!=1:yield 1^f.inverse(w)


def _verified(f,cols,b,c,j,k):
    if _safe(f,cols,b):return b
    if c==0:
        # det(I+M_t E) has degree at most k and is one at t=0.
        # Sum on any (k+1)-flat through zero vanishes when k<d.
        for t in range(1,1<<min(k+1,f.m)):
            s=b^f.inverse(t)
            if _safe(f,cols,s):return s
        raise ArithmeticError("scalar repair failed")
    d=f.m
    g=gcd(d,j)
    basis=_subfield(f,g)
    decode=None
    if g>k:
        if g==1:decode=lambda i:i
        else:
            encode=encoder(basis)
            def multiply(x,y):
                return encode(f.mul(apply_basis(basis,x),apply_basis(basis,y)))
            chart=power_chart(g,encode(1),multiply)
            def decode(i):return apply_basis(basis,chart.decode(i))
    absolute=power_chart(d,1,f.mul)
    bound=min(f.size-1,(2*d+1)**(2*k))
    u=1
    while True:
        for n in _norms(f,basis,decode,g,k,u):
            y=norm_preimage(f,g,n)
            for i in range(1,u+1):
                step=power(f,absolute.decode(i),(1<<j)-1)
                for z in _orbit(f,step,bound):
                    s=b^f.mul(c,f.mul(y,z))
                    if _safe(f,cols,s):return s
        if u==f.size-1:raise ArithmeticError("verified orbit promise failed")
        u=min(2*u,f.size-1)


def find_fit(f,columns,k,b,c,j):
    """Check supplied fit and run both orbit branches even at small degree."""
    cols=_inputs(f,columns,k)
    if any(type(x)!=int or not 0<=x<f.size for x in (b,c)):
        raise ValueError("invalid field coefficient")
    if type(j)!=int or not 1<=j<f.m:raise ValueError("invalid shift exponent")
    residual=[y^f.mul(b,1<<i)^f.mul(c,power(f,1<<i,1<<j)) for i,y in enumerate(cols)]
    rank=len(independent(residual))
    if rank>k:return None
    return _verified(f,cols,b,c,j,rank)


def find_columns(f,columns,k):
    """Return a replayed safe slope or None if no promised fit is recognized."""
    cols=_inputs(f,columns,k)
    if 4*k>=f.m or f.m==1:
        return next(s for s in range(f.size) if _safe(f,cols,s))
    for b,c,j in fits(f,cols,k,include_scalar=True):
        return _verified(f,cols,b,c,j,k)
    return None
