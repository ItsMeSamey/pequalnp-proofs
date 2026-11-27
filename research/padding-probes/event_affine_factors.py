"""Gaussian solving of explicit unary domains and binary allowed relations.

Records are original hashable objects. Optional per-variable dictionaries give
injective integer encodings; records excluded by pins may remain in a dictionary.
Unspecified dictionaries use the given domain iteration order.
"""
from affine_relation import affine_hull, solve_equations


def _omissions(points):
    """Enumerate the affine hull only after its size passed the exception budget."""
    origin=min(points)
    piv={}
    for point in points:
        d=point^origin
        while d:
            p=d.bit_length()-1
            if p not in piv:
                piv[p]=d
                break
            d^=piv[p]
    hull=[origin]
    for d in piv.values():
        hull.extend([x^d for x in hull])
    return sorted(set(hull)-points)


def solve(domains,constraints,output,*,codebooks=None,exception_cap=0,branch_cap=None):
    """Solve both output bits. exception_cap bounds the total missing local words.

    branch_cap bounds Gaussian feasibility calls across both outputs. UNKNOWN
    may include a partial witness; it never certifies absence of the other bit.
    """
    if (type(exception_cap) is not int or exception_cap<0 or branch_cap is not None
            and (type(branch_cap) is not int or branch_cap<0)):
        raise ValueError("invalid affine budgets")
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
    witnesses={}
    def result(status,reason=None):
        out=dict(status=status,witnesses=witnesses,metrics=metrics)
        if reason:
            out["reason"]=reason
        if status=="constant":
            out["value"]=next(iter(witnesses))
        return out
    if any(not points for scope,points in factors):
        return result("empty")
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
    if metrics["exception_count"]>exception_cap:
        return result("unknown","exception cap")
    for scope,points in pending:
        positions=[offset[v]+j for v in scope for j in range(width[v])]
        mask=sum(1<<p for p in positions)
        for hole in _omissions(points):
            target=sum(((hole>>j)&1)<<p for j,p in enumerate(positions))
            forbidden.append((mask,target))

    capped=False
    for value in (0,1):
        if value not in enc[output]:
            continue
        outword=enc[output][value]
        stack=[tuple((1<<(offset[output]+j),(outword>>j)&1) for j in range(width[output]))]
        while stack:
            if branch_cap is not None and metrics["branch_states"]>=branch_cap:
                capped=True
                break
            restrictions=stack.pop()
            metrics["branch_states"]+=1
            assignment=solve_equations(total,tuple(equations)+restrictions)
            if assignment is None:
                continue
            hit=next(((mask,word) for mask,word in forbidden if assignment&mask==word),None)
            if hit is None:
                witness={v:dec[v][(assignment>>offset[v])&((1<<width[v])-1)] for v in domains}
                if witness[output]!=value or any((witness[u],witness[v]) not in pairs for u,v,pairs in relations):
                    raise ArithmeticError("original record assignment failed")
                witnesses[value]=witness
                break
            mask,word=hit
            prefix=list(restrictions)
            metrics["branches"]+=1
            while mask:
                bit=mask&-mask
                same=int(bool(word&bit))
                stack.append(tuple(prefix)+((bit,same^1),))
                prefix.append((bit,same))
                mask^=bit
    if len(witnesses)==2:
        return result("pair")
    if capped:
        return result("unknown","branch cap")
    return result("constant" if witnesses else "empty")
