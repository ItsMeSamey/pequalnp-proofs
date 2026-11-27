"""Optimal codimension plus residual alternating-form rank, over F2."""
from itertools import combinations
from quadratic_target import affine_domain, apply_basis, evaluate_anf, insert, interpolate
from isotropic_hybrid import count as gauss_count


def lagrangians(form):
    """Enumerate s-spaces in 2s coordinates by RREF, filtering for isotropy."""
    d=len(form)
    s=d//2
    for piv in combinations(range(d),s):
        free=[(i,j) for i,k in enumerate(piv) for j in range(k+1,d) if j not in piv]
        for word in range(1<<len(free)):
            rows=[1<<k for k in piv]
            for bit,(i,j) in enumerate(free):
                if word>>bit & 1:
                    rows[i]|=1<<j
            if all(not (apply_basis(form,x)&y).bit_count()%2 for x,y in combinations(rows,2)):
                yield rows


def optimal_split(n,pairs,cap=None):
    """Return (complement, flat, output-column echelon span) or None on cap miss."""
    if cap is not None and (type(cap) is not int or cap<0):
        raise ValueError('invalid cap')
    def search(flat,b):
        d=len(flat)
        def q(x):
            return evaluate_anf(0,[0]*n,pairs,apply_basis(flat,x))
        values=interpolate(q,d)[2]
        span={}
        for v in values.values():
            insert(v,0,span)
        if len(span)<=b:
            return flat,span
        keys=list(span)[:b+1]
        for select in range(1,1<<len(keys)):
            char=apply_basis([1<<k for k in keys],select)
            matrix=[0]*d
            for (i,j),v in values.items():
                if (v&char).bit_count()%2:
                    matrix[i]|=1<<j
                    matrix[j]|=1<<i
            _,rad,piv=affine_domain(d,((row,0) for row in matrix))
            s=len(piv)//2
            assert s and 2*s==len(piv)
            if s>b:
                continue
            quotient=[sum(((matrix[i]>>j)&1)<<h for h,j in enumerate(piv)) for i in piv]
            axes=[1<<j for j in piv]
            radical=[apply_basis(flat,v) for v in rad]
            for lag in lagrangians(quotient):
                smaller=radical+[apply_basis(flat,apply_basis(axes,v)) for v in lag]
                found=search(smaller,b-s)
                if found is not None:
                    return found
        return None
    for budget in range(1+(n if cap is None else min(n,cap))):
        found=search([1<<i for i in range(n)],budget)
        if found is None:
            continue
        flat,span=found
        rows={}
        for x in flat:
            insert(x,0,rows)
        complement=[1<<i for i in range(n) if insert(1<<i,0,rows)]
        return complement,flat,span
    return None


def count(n,constant,linear,pairs,target,cap=None):
    """A structural cap miss returns (None,None,cap+1), a lower bound on optimum."""
    split=optimal_split(n,pairs,cap)
    if split is None:
        return None,None,cap+1
    return gauss_count(n,constant,linear,pairs,target,split_provider=lambda n,pairs:split)
