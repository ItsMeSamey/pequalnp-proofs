"""2-CNF in redundant linear coordinates with bounded parity-check codimension."""
from itertools import combinations,product
from one_defect_clause_closure import solve_clauses
from quadratic_target import affine_domain, apply_basis, insert, parity


def solve(d,flats,*,h_cap=3,layout_cap=729):
    if min(d,h_cap,layout_cap)<0:
        raise ValueError("negative dimension or cap")
    lines=set()
    planes=set()
    physical=[]
    for f in flats:
        if len(f)>2 or any(v<0 or v>=1<<d or c not in (0,1) for v,c in f):
            raise ValueError("invalid exclusion")
        if affine_domain(d,f) is None:
            continue
        form={v:c for v,c in f if v}
        if not form:
            return 'NO',None,{}
        if len(form)==1:
            lines.update(form)
        else:
            (a,x),(b,y)=form.items()
            form[a^b]=x^y
            planes.add(tuple(sorted(form)))
        physical.append(form)
    planes=sorted(planes)
    B=set(lines)
    choices=[]
    for P in planes:
        options=list(combinations(P,2))
        B.update(min(options,key=lambda p:len(set(p)-B)))
        choices.append(options)
    exact_layout=3**len(planes)<=layout_cap
    if exact_layout:
        for pick in product(*choices):
            trial=lines.union(*pick)
            if len(trial)<len(B):
                B=trial
    B=sorted(B)
    index={v:i for i,v in enumerate(B)}
    basis={}
    checks=[]
    from quadratic_target import reduce_vector
    for i,v in enumerate(B):
        r,c=reduce_vector(v,basis)
        if not r:
            checks.append(c^(1<<i))
        else:
            insert(v,1<<i,basis)
    h=len(checks)
    stats=dict(h=h,exact_layout=exact_layout)
    if h>h_cap:
        return 'UNKNOWN',None,stats
    H=[]
    for form in physical:
        selected=[2*index[v]+c for v,c in form.items() if v in index][:2]
        H.append((selected[0],selected[-1]))
    N=len(B)
    base=solve_clauses(N,H)
    if base is None:
        return 'NO',None,stats
    flips=[2*i+1-(base>>i&1) for i in range(N)]
    for size in range(min(h,N)+1):
        for p in combinations(flips,size):
            if size and solve_clauses(N,H,p) is None:
                continue
            z=base
            if size:
                for i,a in enumerate(flips):
                    if solve_clauses(N,H,(*p,a^1)) is None:
                        z^=1<<i
            if all(not parity(c&z) for c in checks):
                y=affine_domain(d,[(v,z>>i&1) for i,v in enumerate(B)])[0]
                return 'YES',y,stats
    return 'NO',None,stats


def search(rows,beta,pivot=None,**kwargs):
    n=len(rows)
    if any(v<0 or v>=1<<n for v in (*rows,beta)):
        raise ValueError("invalid matrix or mark")
    if not beta:
        return 'NO',None,{}
    if pivot is None:
        pivot=(beta&-beta).bit_length()-1
    if not 0<=pivot<n or not beta>>pivot&1:
        raise ValueError("pivot must be marked")
    origin=1<<pivot
    dirs=[(1<<i)^(((beta>>i)&1)<<pivot) for i in range(n) if i!=pivot]
    def eq(v):
        return sum(parity(v&x)<<i for i,x in enumerate(dirs)),1^parity(v&origin)
    status,y,stats=solve(len(dirs),[(eq(1<<i),eq(r)) for i,r in enumerate(rows)],**kwargs)
    return status,None if y is None else origin^apply_basis(dirs,y),stats
