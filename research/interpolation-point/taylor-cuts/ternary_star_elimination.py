"""Exact avoidance of homogeneous ternary hyperplanes by small cocircuit elimination."""
from itertools import combinations,product
from ternary_frame import sub,reduce,_projective


def dot(x,y):
    return sum(a*b for a,b in zip(x,y))%3


def kernel(d,rows):
    pivots={}
    for row in rows:
        v=reduce(row,pivots)
        p=next((i for i,a in enumerate(v) if a),None)
        if p is not None:
            pivots[p]=tuple(a*v[p]%3 for a in v)
    basis=[]
    for j in range(d):
        if j not in pivots:
            v=[0]*d
            v[j]=1
            for p,w in sorted(pivots.items(),reverse=True):
                v[p]=-dot(w,v)%3
            basis.append(tuple(v))
    return basis


def lift(basis,x,d):
    return tuple(sum(a*v[i] for a,v in zip(x,basis))%3 for i in range(d))


def avoid(d,rows,*,max_star=3):
    """Return a point avoiding all listed normal hyperplanes, or None."""
    if max_star not in (2,3):
        raise ValueError("supported star sizes are two and three")
    rows=list(dict.fromkeys(_projective(v) for v in rows))
    if any(len(v)!=d for v in rows):
        raise ValueError("wrong normal dimension")
    if any(not any(v) for v in rows):
        return None
    for size in range(1,min(max_star,len(rows))+1):
        for ids in combinations(range(len(rows)),size):
            keep=[v for j,v in enumerate(rows) if j not in ids]
            w=next((u for u in kernel(d,keep) if any(dot(rows[i],u) for i in ids)),None)
            if w is None:
                continue
            p=next(i for i,a in enumerate(w) if a)
            active=[v for v in rows if dot(v,w)]
            stationary=[v[:p]+v[p+1:] for v in rows if not dot(v,w)]
            roots=[tuple(-a*dot(v,w)%3 for a in v[:p]+v[p+1:]) for v in active]
            equalities=[None] if len(roots)<=2 else [sub(a,b,1) for a,b in combinations(roots,2)]
            for eq in equalities:
                if eq is None:
                    base=avoid(d-1,stationary,max_star=max_star)
                else:
                    basis=kernel(d-1,[eq])
                    smaller=[tuple(dot(v,u) for u in basis) for v in stationary]
                    point=avoid(len(basis),smaller,max_star=max_star)
                    base=None if point is None else lift(basis,point,d-1)
                if base is not None:
                    t=next(a for a in range(3) if all(a!=dot(v,base) for v in roots))
                    x=base[:p]+(0,)+base[p:]
                    return tuple((a+t*b)%3 for a,b in zip(x,w))
            return None
    return next((x for x in product(range(3),repeat=d) if all(dot(v,x) for v in rows)),None)
