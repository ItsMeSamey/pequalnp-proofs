"""Find a safe scalar in a small affine fixed locus of a raw graph stabilizer."""
from itertools import combinations
from math import gcd
from additive_safe_slope import _safe
from affine_binomial import power
from projective_stabilizer_slope import transforms
from quadratic_centroid import zero_combinations
from quadratic_target import affine_domain,apply_basis


def _compose(f,p,q):
    """p after q, triples (translation, multiplier, Frobenius exponent)."""
    b,a,j=p
    y,x,k=q
    return b^f.mul(a,power(f,y,1<<j)), f.mul(a,power(f,x,1<<j)), (j+k)%f.m


def _power(f,phi,M):
    result=(0,1,0)
    while M:
        if M&1:result=_compose(f,result,phi)
        phi=_compose(f,phi,phi)
        M>>=1
    return result


def _transform(f,cols,j):
    d=f.m
    mask=f.size-1
    basis=zero_combinations(transforms(f,cols,j),lambda x:(x>>d)&mask)
    # Invertibility on this space is a nonzero product of two field-linear
    # projections in the binary basis coefficients, of Boolean degree at most 2.
    for n in (1,2):
        for subset in combinations(basis,n):
            v=subset[0] if n==1 else subset[0]^subset[1]
            a=v&mask
            e=(v>>(3*d))&mask
            if a and e:
                c=(v>>(2*d))&mask
                return a,0,c,e
    return None


def fixed_locus(f,columns):
    """Return (j,T,psi,offset,basis) or None when the affine search abstains."""
    cols=tuple(columns)
    d=f.m
    if len(cols)!=d or any(type(x)!=int or not 0<=x<f.size for x in cols):
        raise ValueError("invalid original columns")
    odd=d//(d&-d)
    def order2(j):
        n=d//gcd(d,j)
        return n&-n
    for j in sorted(range(1,d),key=order2,reverse=True):
        size=order2(j)
        if size==1:break
        T=_transform(f,cols,j)
        if T is None:continue
        a,_,c,e=T
        inv=f.inverse(a)
        psi=_power(f,(f.mul(c,inv),f.mul(e,inv),j),(f.size-1)*odd)
        b,v,k=psi
        linear=[(1<<i)^f.mul(v,power(f,1<<i,1<<k)) for i in range(d)]
        eq=[(sum(((x>>i)&1)<<j for j,x in enumerate(linear)),(b>>i)&1) for i in range(d)]
        fixed=affine_domain(d,eq)
        if fixed is None:raise ArithmeticError("odd invariant set has no fixed point")
        offset,basis,_=fixed
        if len(basis)>d//size:raise ArithmeticError("fixed locus exceeded dimension bound")
        return j,T,psi,offset,tuple(basis)
    return None


def find_columns(f,columns):
    cols=tuple(columns)
    chart=fixed_locus(f,cols)
    if chart is None:return None
    _,_,_,offset,basis=chart
    for mask in range(1<<len(basis)):
        s=offset^apply_basis(basis,mask)
        if _safe(f,cols,s):return s
    raise ArithmeticError("fixed locus failed original rank replay")
