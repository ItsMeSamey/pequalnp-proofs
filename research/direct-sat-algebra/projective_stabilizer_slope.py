"""Find finite safe slopes from projective semilinear stabilizers of a raw graph."""
from itertools import combinations
from additive_safe_slope import _safe
from commuting_spread import kernel_columns
from quadratic_target import apply_basis


def transforms(f,columns,j):
    """Binary basis of T with T F^j(U) contained in U (packed row-major entries)."""
    d=f.m
    def frob(x):
        for _ in range(j):
            x=f.mul(x,x)
        return x
    X=[frob(1<<i) for i in range(d)]
    Y=[frob(c) for c in columns]
    equations=[]
    for entry in range(4):
        images=(X,Y)[entry%2]
        for k in range(d):
            values=[f.mul(1<<k,v) for v in images]
            if entry<2:
                values=[apply_basis(columns,v) for v in values]
            equations.append(sum(v<<(i*d) for i,v in enumerate(values)))
    return kernel_columns(equations)


def find_columns(f,columns,*,certificate=False):
    """Return one finite safe slope or None when this stabilizer test is exhausted."""
    cols=tuple(columns)
    d=f.m
    if len(cols)!=d or any(not isinstance(v,int) or not 0<=v<f.size for v in cols):
        raise ValueError("invalid original columns")
    mask=f.size-1
    for j in range(d):
        basis=transforms(f,cols,j)
        for k in (1,2,3):
            for selection in combinations(basis,k):
                code=0
                for v in selection:
                    code^=v
                a,b,c,e=[(code>>(i*d))&mask for i in range(4)]
                if not b or f.mul(a,e)==f.mul(b,c):
                    continue
                slope=f.mul(e,f.inverse(b))
                if not _safe(f,cols,slope):
                    raise ArithmeticError("transformed infinity failed original rank replay")
                return (slope,j,(a,b,c,e)) if certificate else slope
    return None
