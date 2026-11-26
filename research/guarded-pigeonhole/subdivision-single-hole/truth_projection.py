"""Exact bounded affine-scope elimination and common-radical quadratic projection."""
from itertools import combinations


def parity(x):
    return x.bit_count()&1


def echelon(vectors):
    piv={}
    for i,row in enumerate(vectors):
        label=1<<i
        while row and row.bit_length() in piv:
            v,w=piv[row.bit_length()]
            row^=v
            label^=w
        if row:piv[row.bit_length()]=(row,label)
    return piv


def coordinates(x,piv):
    label=0
    while x:
        v,w=piv[x.bit_length()]
        x^=v
        label^=w
    return label


def kernel(rows,n):
    piv=echelon(rows)
    out=[]
    for j in range(n):
        if j+1 in piv:continue
        x=1<<j
        for k,(v,_) in sorted(piv.items()):
            if parity(x&v):x^=1<<(k-1)
        out.append(x)
    return out


def index(forms,x):
    return sum(parity(f&x)<<i for i,f in enumerate(forms))


def bucket(factors,j,cap):
    """Factor=(tuple of linear normals, set of accepted evaluation masks)."""
    active=[(norms,ok) for norms,ok in factors if any(f>>j&1 for f in norms)]
    rest=[f for f in factors if f not in active]
    if not active:return rest
    raw=[v for ns,_ in active for v in ns]
    pivot=next(v for v in raw if v>>j&1)
    residual=[v^pivot if v>>j&1 else v for v in raw]
    piv=echelon(residual)
    if len(piv)+1>cap:raise ValueError("affine bucket exceeds budget")
    base=tuple(v for v,_ in piv.values())
    full=base+(pivot,)
    span=echelon(full)
    tables=[(tuple(coordinates(f,span) for f in ns),ok) for ns,ok in active]
    def legal(assignment):
        return all(index(ns,assignment) in ok for ns,ok in tables)
    ok={a for a in range(1<<len(base)) if legal(a) or legal(a|(1<<len(base)))}
    return rest+[(base,ok)]


def quadratic_indicator(allowed,n):
    """For an exact single-equation fit, return its quadratic rejection ANF or None."""
    a=[int(x not in allowed) for x in range(1<<n)]
    for j in range(n):
        for x in range(1<<n):
            if x>>j&1:a[x]^=a[x^(1<<j)]
    terms={i for i,b in enumerate(a) if b}
    return terms if all(t.bit_count()<=2 for t in terms) else None


def evaluate(poly,x):
    return sum((t&x)==t for t in poly)&1


def truth_vector(polys,x):
    return sum(evaluate(p,x)<<j for j,p in enumerate(polys))


def radical_projection(polys,n):
    """Return complement coordinates, output checks, log2 uniform multiplicity, radical."""
    rows=[]
    for p in polys:
        for i in range(n):
            v=0
            for t in p:
                if t.bit_count()==2 and t>>i&1:v^=t^(1<<i)
            if v:rows.append(v)
    R=kernel(rows,n)
    piv=echelon(R)
    complement=[1<<j for j in range(n) if j+1 not in piv]
    zero=truth_vector(polys,0)
    deltas=[truth_vector(polys,v)^zero for v in R]
    checks=kernel(deltas,len(polys))
    reduced=[]
    for mask in checks:
        p=set()
        for i,q in enumerate(polys):
            if mask>>i&1:p^=q
        projected=set()
        for t in p:
            u=sum(1<<j for j,b in enumerate(complement) if t&b)
            if u.bit_count()==t.bit_count():projected.add(u)
        if projected:reduced.append(projected)
    return complement,reduced,len(R)-len(echelon(deltas)),R


def walsh(p,n):
    p=set(p)
    while True:
        uv=next((t for t in p if t.bit_count()==2),None)
        if uv is None:
            if p-{0}:return 0
            return -(1<<n) if 0 in p else 1<<n
        u=uv&-uv
        v=uv^u
        a=[t^u for t in p if t&u and t!=uv]
        b=[t^v for t in p if t&v and t!=uv]
        p={t for t in p if not t&uv}
        for i in a:
            for j in b:p.symmetric_difference_update({i|j})
        n-=1


def count_polys(polys,n):
    tables=[set()]
    for p in polys:tables.extend([q^p for q in tables])
    return sum(walsh(p,n) for p in tables)//len(tables)


def fit_factor(normals,allowed):
    """Return exact quadratic equations in original coordinates, or None."""
    k=len(normals)
    q=quadratic_indicator(allowed,k)
    if q is not None:
        local=[q]
    else:
        monomials=[s for s in range(1<<k) if s.bit_count()<=2]
        evaluations=[sum(int((s&x)==s)<<i for i,s in enumerate(monomials)) for x in allowed]
        local=[{s for i,s in enumerate(monomials) if v>>i&1}
               for v in kernel(evaluations,len(monomials))]
        if any(x not in allowed and not truth_vector(local,x) for x in range(1<<k)):
            return None
    translated=[]
    for p in local:
        ans=set()
        for term in p:
            value={0}
            for j,form in enumerate(normals):
                if not term>>j&1:continue
                new=set()
                for old in value:
                    v=form
                    while v:
                        b=v&-v
                        new.symmetric_difference_update({old|b})
                        v^=b
                value=new
            ans^=value
        if ans:translated.append(ans)
    return translated
