"""Recognize a shared linear coordinate system for codimension-at-most-two exclusions."""
from itertools import combinations
from one_defect_clause_closure import solve_clauses
from quadratic_target import affine_domain, apply_basis, insert, parity


def layout(lines,planes):
    """Return independent coordinate normals, or None for a genuine obstruction."""
    planes=sorted({tuple(sorted(P)) for P in planes})
    forced=set(lines)
    for P,Q in combinations(planes,2):
        forced.update(set(P)&set(Q))
    chosen=sorted(forced)
    for P in planes:
        local=[v for v in P if v in forced]
        if len(local)>2:
            return None
        chosen.extend(v for v in [w for w in P if w not in forced][:2-len(local)])
    basis={}
    if any(not insert(v,0,basis) for v in chosen):
        return None
    return chosen


def solve_flats(d,flats):
    """Each excluded flat is an intersection of up to two scalar equations."""
    actual=[]
    lines=set()
    planes=set()
    for flat in flats:
        if len(flat)>2 or any(not 0<=v<1<<d or c not in (0,1) for v,c in flat):
            raise ValueError("invalid flat")
        if affine_domain(d,flat) is None:
            continue
        form=dict((v,c) for v,c in flat if v)
        if not form:
            return 'NO',None
        if len(form)==1:
            normal=next(iter(form))
            lines.add(normal)
            actual.append(form)
        else:
            (a,x),(b,y)=form.items()
            form[a^b]=x^y
            planes.add(tuple(sorted(form)))
            actual.append(form)
    coords=layout(lines,planes)
    if coords is None:
        return 'UNKNOWN',None
    forbidden=[]
    for form in actual:
        literals=[2*i+form[v] for i,v in enumerate(coords) if v in form]
        assert 1<=len(literals)<=2
        forbidden.append((literals[0],literals[-1]))
    mask=solve_clauses(len(coords),forbidden)
    if mask is None:
        return 'NO',None
    return 'YES',affine_domain(d,[(v,(mask>>i)&1) for i,v in enumerate(coords)])[0]


def search(rows,beta,pivot=None):
    """A pivot only parametrizes the mark: existence of a coordinate layout is invariant."""
    n=len(rows)
    if any(v<0 or v>=1<<n for v in (*rows,beta)):
        raise ValueError("invalid matrix or mark")
    if not beta:
        return 'NO',None
    if pivot is None:
        pivot=(beta&-beta).bit_length()-1
    if not 0<=pivot<n or not beta>>pivot&1:
        raise ValueError("pivot must be marked")
    point=1<<pivot
    dirs=[(1<<i)^(((beta>>i)&1)<<pivot) for i in range(n) if i!=pivot]
    def equation(v):
        return sum(parity(v&x)<<i for i,x in enumerate(dirs)),1^parity(v&point)
    flats=[(equation(1<<i),equation(v)) for i,v in enumerate(rows)]
    status,y=solve_flats(len(dirs),flats)
    if y is None:
        return status,None
    z=point^apply_basis(dirs,y)
    assert parity(z&beta) and all(not(z>>i&1 and parity(z&r)) for i,r in enumerate(rows))
    return status,z


def search_with_closure(rows,beta):
    """After a failed invariant layout, try the coordinate-sensitive closure at every pivot."""
    from one_defect_affine_closure import search as closure
    status,z=search(rows,beta)
    if status=='UNKNOWN':
        for j in range(len(rows)):
            if beta>>j&1:
                status,z,_=closure(rows,beta,j)
                if status!='UNKNOWN':
                    break
    return status,z
