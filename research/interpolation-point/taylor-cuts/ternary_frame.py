"""Three-coloring by affine triangle frames over GF(3)."""


def sub(v,w,a):
    return tuple((x-a*y)%3 for x,y in zip(v,w))


def reduce(v,basis):
    for p,w in sorted(basis.items()):
        if v[p]:
            v=sub(v,w,v[p])
    return v


def _projective(v):
    scalar=next((x for x in v if x),1)
    return tuple((x*scalar)%3 for x in v)


def kernel_obstruction(cols):
    """Certificate indices refer to original slope variables, after parallel peeling."""
    ids=sorted(cols)
    if not ids:
        return None
    pivots={}
    for row in zip(*(cols[i] for i in ids)):
        w=reduce(row,pivots)
        p=next((j for j,a in enumerate(w) if a),None)
        if p is not None:
            pivots[p]=tuple(a*w[p]%3 for a in w)
    free=[j for j in range(len(ids)) if j not in pivots]
    evaluations=[[0]*len(free) for _ in ids]
    for j,f in enumerate(free):
        evaluations[f][j]=1
        for p,w in sorted(pivots.items(),reverse=True):
            evaluations[p][j]=-sum(a*v[j] for a,v in zip(w,evaluations))%3
    representatives={}
    for i,v in zip(ids,evaluations):
        u=_projective(v)
        if not any(u):
            return {"kind":"zero","indices":(i,),"functionals":(u,)}
        representatives.setdefault(u,i)
    keys=list(representatives)
    for j,u in enumerate(keys):
        for v in keys[:j]:
            directions=(u,v,_projective(sub(u,v,1)),_projective(sub(u,v,2)))
            if all(w in representatives for w in directions):
                return {"kind":"pencil","indices":tuple(representatives[w] for w in directions),
                        "functionals":directions}
    return None


def palettes(n,edges):
    adj=[set() for _ in range(n)]
    remaining=set(tuple(sorted(e)) for e in edges)
    for a,b in remaining:
        if not 0<=a<=b<n:
            raise ValueError("invalid endpoint")
        if a==b:
            return None
        adj[a].add(b)
        adj[b].add(a)
    frames=[]
    while remaining:
        root=min(remaining)
        f={root[0]:0,root[1]:1}
        stack=[root]
        remaining.remove(root)
        while stack:
            a,b=stack.pop()
            if f[a]==f[b]:
                return None
            for c in adj[a]&adj[b]:
                x=(-f[a]-f[b])%3
                if f.setdefault(c,x)!=x:
                    return None
                for k in (a,b):
                    edge=tuple(sorted((k,c)))
                    if edge in remaining:
                        remaining.remove(edge)
                        stack.append(edge)
        frames.append(f)
    return frames


def color(n,edges,*,cap=None,use_prism=False,check_pencil=True,transfer_rank=None,four_row_high=None,
          global_b=None,global_h=0,owner_kappa=0,planar_character_cap=None,global_rounds=0):
    """Return status, coloring or None, and metrics. Cap limits 3**residual_rank."""
    if type(n) is not int or n<0 or cap is not None and (type(cap) is not int or cap<0):
        raise ValueError("invalid dimension or cap")
    if four_row_high is not None and (type(four_row_high) is not int or four_row_high<0):
        raise ValueError("four_row_high must be a nonnegative integer")
    for value in (global_b,planar_character_cap):
        if value is not None and (type(value) is not int or value<0):
            raise ValueError("invalid optional global matching cap")
    for value in (global_h,owner_kappa,global_rounds):
        if type(value) is not int or value<0:
            raise ValueError("invalid global matching cap")
    edges=tuple(edges)
    frames=palettes(n,edges)
    stats={"frames":0,"peeled_groups":0,"residual_rank":0}
    if frames is None:
        return "UNSAT",None,stats
    m=stats["frames"]=len(frames)
    memberships=[[] for _ in range(n)]
    for i,f in enumerate(frames):
        for v,x in f.items():
            memberships[v].append((i,x))
    translations={}
    rows=[]
    for occ in memberships:
        for j,b in occ[1:]:
            i,a=occ[0]
            row=[0]*(2*m)
            row[i],row[j],row[m+i],row[m+j]=1,2,a,-b%3
            row=reduce(row,translations)
            p=next((k for k in range(m) if row[k]),None)
            if p is None:
                if any(row[m:]):
                    rows.append(row[m:])
            else:
                translations[p]=tuple(x*row[p]%3 for x in row)
    stats["prism_rows"]=0
    classes=tuple((i,1) for i in range(m))
    if use_prism:
        from ternary_prism_rows import prism_rows,orientation_classes
        relations=prism_rows(edges,frames)
        stats["prism_rows"]=len(relations)
        classes=orientation_classes(m,relations)
        if classes is None:
            stats["certificate"]={"kind":"inconsistent signed cycle","relations":relations}
            return "UNSAT",None,stats
    representatives=sorted({rep for rep,_ in classes})
    cols={rep:[0]*len(rows) for rep in representatives}
    for i,(rep,scale) in enumerate(classes):
        for k,row in enumerate(rows):
            cols[rep][k]=(cols[rep][k]+scale*row[i])%3
    corrections=[]
    slopes={}
    raw_cols=cols.copy() if four_row_high is not None or global_b is not None else None
    while True:
        groups={}
        for i,col in list(cols.items()):
            p=next((j for j,x in enumerate(col) if x),None)
            if p is None:
                slopes[i]=1
                del cols[i]
            else:
                groups.setdefault(tuple(x*col[p]%3 for x in col),[]).append(i)
        group=next(((v,ids) for v,ids in groups.items() if len(ids)>=2),None)
        if group is None:
            break
        v,ids=group
        p=next(j for j,x in enumerate(v) if x)
        scales={i:cols.pop(i)[p] for i in ids}
        corrections.append((scales,{i:w[p] for i,w in cols.items() if w[p]}))
        cols={i:sub(w,v,w[p]) for i,w in cols.items()}
        stats["peeled_groups"]+=1
    basis={}
    for v in cols.values():
        w=reduce(v,basis)
        p=next((i for i,a in enumerate(w) if a),None)
        if p is not None:
            basis[p]=tuple(a*w[p]%3 for a in w)
    rank=stats["residual_rank"]=len(basis)
    if check_pencil and rank:
        certificate=kernel_obstruction(cols)
        if certificate is not None:
            stats["certificate"]=certificate
            return "UNSAT",None,stats
    raw_signs=None
    if raw_cols is not None and rank:
        ids=tuple(raw_cols)
        # Equivalent scalar multiples impose one constraint.
        system=tuple(dict.fromkeys(_projective(row) for row in zip(*raw_cols.values()) if any(row)))
        if four_row_high is not None:
            from ternary_four_signs import solve
            status,signs,metrics=solve(system,n=len(ids),high_cap=four_row_high)
            stats["four_row"]={**metrics,"status":status}
            if status=="UNSAT":
                return status,None,stats
            if status=="SAT":
                raw_signs=dict(zip(ids,signs,strict=True))
        if raw_signs is None and global_b is not None:
            from ternary_global_rows import solve as solve_global
            from ternary_matching_portfolio import search as branch_search
            from functools import partial
            from secrets import randbelow
            metrics=dict.fromkeys(("owner_calls","planar_calls","hull_calls","random_calls"),0)
            branch=partial(branch_search,owner_kappa=owner_kappa,planar_cap=planar_character_cap,
                           rounds=global_rounds,randbelow_fn=randbelow,metrics=metrics)
            status,signs=solve_global(len(ids),system,b=global_b,h=global_h,branch_solver=branch)
            stats["global_matching"]={**metrics,"status":status}
            if status=="UNSAT":
                return status,None,stats
            if status=="SAT":
                raw_signs=dict(zip(ids,signs,strict=True))
    if raw_signs is not None:
        slopes=raw_signs
        corrections=[]
    elif transfer_rank is not None:
        from ternary_transfer_condition import full_support
        status,signs,metrics=full_support(cols,search_rank=transfer_rank,cap=cap)
        stats.update(metrics)
        if status!="SAT":
            return status,None,stats
        slopes.update(signs)
    else:
        if rank and cap is not None and 3**rank>cap:
            return "UNKNOWN",None,stats
        zero=(0,)*rank
        states={zero:0}
        for i,v in cols.items():
            v=tuple(v[p] for p in sorted(basis))
            nxt={}
            for state,mask in states.items():
                for s in (1,2):
                    nxt.setdefault(sub(state,v,-s),mask | ((s-1)<<i))
            states=nxt
        if zero not in states:
            return "UNSAT",None,stats
        for i in cols:
            slopes[i]=1+((states[zero]>>i)&1)
    for scales,rest in reversed(corrections):
        need=-sum(a*slopes[i] for i,a in rest.items())
        ids=list(scales)
        for i in ids[2:]:
            slopes[i]=1
            need-=scales[i]
        i,j=ids[:2]
        slopes[i],slopes[j]=next((s,t) for s in (1,2) for t in (1,2)
                                 if (s*scales[i]+t*scales[j]-need)%3==0)
    slopes={i:(slopes[rep]*scale)%3 for i,(rep,scale) in enumerate(classes)}
    values=[0]*m+[slopes[i] for i in range(m)]
    for p,row in sorted(translations.items(),reverse=True):
        values[p]=-sum(a*b for a,b in zip(row,values))%3
    result=[0]*n
    for vertex,occ in enumerate(memberships):
        if occ:
            i,a=occ[0]
            result[vertex]=(values[i]+slopes[i]*a)%3
    if any(result[a]==result[b] for a,b in edges):
        raise ArithmeticError("invalid reconstructed coloring")
    return "SAT",tuple(result),stats
