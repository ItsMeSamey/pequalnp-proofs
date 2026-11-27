"""Exact subfield-line safe-slope search from a raw semilinear residue class."""
from math import gcd
from additive_safe_slope import _safe
from affine_binomial import power
from deterministic_norm_lift import norm_preimage
from hidden_product_network import encoder
from product_slack import linearized
from punctured_chart_witness import power_chart
from quadratic_centroid import zero_combinations
from quadratic_target import apply_basis


def field_basis(f,e):
    return zero_combinations([1<<i for i in range(f.m)],lambda x:x^power(f,x,1<<e))


def solve(f,columns):
    cols=tuple(columns)
    if len(cols)!=f.m or any(type(x)!=int or not 0<=x<f.size for x in cols):
        raise ValueError("invalid raw binary columns")
    coeff=linearized(f,cols)
    b=coeff[0]
    if _safe(f,cols,b):
        return b
    support=[i for i in range(1,f.m) if coeff[i]]
    if not support:
        return b^1
    e=f.m
    for i in support:
        e=gcd(e,i-support[0])
    g=gcd(e,support[0])
    fixed=field_basis(f,g)
    if e==1:
        return b^1 if _safe(f,cols,b^1) else None
    Lbasis=field_basis(f,e)
    enc=encoder(Lbasis)
    def mul(x,y):
        return enc(f.mul(apply_basis(Lbasis,x),apply_basis(Lbasis,y)))
    chart=power_chart(e,enc(1),mul)
    for k in range(1,min(1<<g,f.m//e+1)):
        target=apply_basis(fixed,k)
        local=chart.encode(enc(target))
        z=norm_preimage(chart.field,g,local)
        slope=b^apply_basis(Lbasis,chart.decode(z))
        if _safe(f,cols,slope):
            return slope
    return None
