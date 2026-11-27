"""Compile finite-domain factors to parity equations and forbidden coordinate cylinders."""
from affine_relation import affine_hull
from event_affine_factors import _omissions


def compile_factors(domains,constraints,output,*,codebooks=None,omission_cap=None):
    if omission_cap is not None and (type(omission_cap) is not int or omission_cap<0):
        raise ValueError("invalid omission cap")
    domains={v:tuple(D) for v,D in domains.items()}
    if output not in domains or any(type(bit) not in (int,bool) or bit not in (0,1) for bit in domains[output]):
        raise ValueError("invalid terminal bit domain")
    custom={} if codebooks is None else dict(codebooks)
    if custom.keys()-domains.keys():
        raise ValueError("codebook for unknown variable")
    enc,dec,width,offset={},{},{},{}
    total=0
    for v,D in domains.items():
        if len(set(D))!=len(D):
            raise ValueError("duplicate domain record")
        book=dict(custom[v]) if v in custom else {x:i for i,x in enumerate(D)}
        if (not set(D)<=book.keys() or any(type(a) is not int or a<0 for a in book.values())
                or len(set(book.values()))!=len(book)):
            raise ValueError("incomplete or noninjective integer codebook")
        enc[v]={x:book[x] for x in D}
        dec[v]={a:x for x,a in enc[v].items()}
        width[v]=max((a.bit_length() for a in book.values()),default=0)
        offset[v]=total
        total+=width[v]
    factors=[((v,),set(dec[v])) for v in domains]
    relations=[]
    for u,v,allowed in constraints:
        if u not in domains or v not in domains:
            raise ValueError("constraint on unknown variable")
        pairs=frozenset((x,y) for x,y in allowed if x in enc[u] and y in enc[v])
        relations.append((u,v,pairs))
        if u==v:
            factors.append(((u,),{enc[u][x] for x,y in pairs if x==y}))
        else:
            factors.append(((u,v),{enc[u][x]|(enc[v][y]<<width[u]) for x,y in pairs}))
    metrics=dict(bits=total,factors=len(factors),exception_count=0,nonaffine_factors=0,
                 equations=0,branches=0,branch_states=0,codebook_entries=sum(map(len,enc.values())))
    if any(not points for scope,points in factors):
        return dict(status="empty",metrics=metrics)
    equations=[]
    forbidden=[]
    pending=[]
    for scope,points in factors:
        size=sum(width[v] for v in scope)
        eq,dim=affine_hull(points,size)
        holes=(1<<dim)-len(points)
        metrics["exception_count"]+=holes
        metrics["nonaffine_factors"]+=int(bool(holes))
        def scatter(word):
            packed=0
            for v in scope:
                packed|=(word&((1<<width[v])-1))<<offset[v]
                word>>=width[v]
            return packed
        equations.extend((scatter(m),b) for m,b in eq)
        if holes:
            pending.append((scope,points))
    metrics["equations"]=len(equations)
    if omission_cap is not None and metrics["exception_count"] > omission_cap:
        return dict(status="unknown",reason="omission cap",metrics=metrics)
    for scope,points in pending:
        positions=[offset[v]+j for v in scope for j in range(width[v])]
        mask=sum(1<<p for p in positions)
        for hole in _omissions(points):
            target=sum(((hole>>j)&1)<<p for j,p in enumerate(positions))
            forbidden.append((mask,target))

    return dict(status="ok",metrics=metrics,width=total,equations=tuple(equations),
                cylinders=tuple(sorted(set(forbidden))),enc=enc,dec=dec,offset=offset,
                widths=width,relations=relations)
