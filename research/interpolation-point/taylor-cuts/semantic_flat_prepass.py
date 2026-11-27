"""Exact local affine hull of each duplicate-normal-space group of forbidden events."""
from affine_cell_energy import solve,dot
from affine_cover_solver import insert,reduce_equation
from clause_rank_drop import _image


def preprocess(n,clauses,xor_rows=()):
    """Return (UNSAT/AFFINE/OPEN, augmented original equations, metrics).
    AFFINE means every assignment of the returned affine system satisfies the CNF.
    """
    if type(n) is not int or n<0:
        raise ValueError("invalid dimension")
    clauses=[tuple(c) for c in clauses]
    if any(type(l) is not int or not 1<=abs(l)<=n for c in clauses for l in c):
        raise ValueError("invalid literal")
    eq=list(xor_rows)
    stats={"passes":0,"scanned_syndromes":0,"new_rank":0}
    while True:
        stats["passes"]+=1
        chart=solve(n,eq)
        if chart is None:
            return "UNSAT",eq,stats
        origin,directions=chart
        d=len(directions)
        groups={}
        for c in clauses:
            basis={}
            for l in c:
                v=1<<(abs(l)-1)
                if not insert(_image(v,directions),int(l<0)^dot(v,origin),basis):
                    break
            else:
                canon={}
                for pivot in sorted(basis):
                    canon[pivot]=reduce_equation(*basis[pivot],canon)
                normals=tuple(a for a,b in canon.values())
                word=sum(b<<i for i,(a,b) in enumerate(canon.values()))
                groups.setdefault(normals,set()).add(word)
        if not groups:
            return "AFFINE",eq,stats
        additions={}
        for normals,blocked in groups.items():
            r=len(normals)
            # Equivalent to 2^r > 2|blocked| without creating a huge table.
            if r >= (2*len(blocked)).bit_length():
                continue
            stats["scanned_syndromes"]+=1<<r
            allowed=[u for u in range(1<<r) if u not in blocked]
            if not allowed:
                return "UNSAT",eq,stats
            _,checks=solve(r,((u^allowed[0],0) for u in allowed[1:]))
            for h in checks:
                normal=0
                for j,a in enumerate(normals):
                    if h>>j&1:
                        normal^=a
                if not insert(normal,dot(h,allowed[0]),additions):
                    return "UNSAT",eq,stats
        if not additions:
            return "OPEN",eq,stats
        for normal,b in additions.values():
            lift=solve(n,[(k,normal>>j&1) for j,k in enumerate(directions)])[0]
            eq.append((lift,b^dot(lift,origin)))
        stats["new_rank"]+=len(additions)
