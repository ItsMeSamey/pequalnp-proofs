"""Optimal rank-drop plus exceptions on a hard XOR domain."""
from itertools import product
from affine_cell_energy import dot,solve
from affine_cover_solver import insert
from affine_union_cache import canonical
from clause_rank_drop import _image,_combination,_basis,_restrict


def _search(kernel,groups,ignored,budget,stats,prune):
    stats["search_nodes"]+=1
    for j,group in enumerate(groups):
        if j in ignored:continue
        rows=_basis(_image(a,kernel) for a,_ in group[0])
        if len(rows)>1:break
    else:return kernel,[],ignored
    price=len(group).bit_length()
    r=len(rows)
    if price<=budget and (not prune or price<r-1):
        child=_search(kernel,groups,ignored|{j},budget-price,stats,prune)
        if child is not None:return child
    if r-1>budget:return None
    for mask in range(1,1<<r):
        pivot=mask.bit_length()-1
        normals=[a^(rows[pivot] if mask>>i&1 else 0) for i,a in enumerate(rows) if i!=pivot]
        small,complement=_restrict(kernel,normals)
        child=_search(small,groups,ignored,budget-r+1,stats,prune)
        if child is not None:
            final,more,excluded=child
            return final,complement+more,excluded
    return None


def _avoid(d,forced,groups):
    total=0
    for choices in product(*(range(len(g)+1) for g in groups)):
        eq=forced.copy()
        for group,j in zip(groups,choices):
            if j and not all(insert(a,b,eq) for a,b in group[j-1]):break
        else:
            term=1<<(d-len(eq))
            total+=-term if sum(bool(j) for j in choices)%2 else term
    return total


def count(n,clauses,xor_rows=(),*,cap=None,optimal=True,group_equal=False,prune=True):
    """Return (count,witness,metrics). None count means a budget miss."""
    if type(n) is not int or n<0 or cap is not None and (type(cap) is not int or cap<0):
        raise ValueError("invalid dimension or cap")
    if not optimal:raise ValueError("this backend implements optimal search")
    clauses=tuple(tuple(c) for c in clauses); xor_rows=tuple(xor_rows)
    if any(type(l) is not int or not 1<=abs(l)<=n for c in clauses for l in c):
        raise ValueError("invalid literal")
    chart=solve(n,xor_rows)
    stats=dict(search_nodes=0,cosets=0,optimum=None,discarded_events=0)
    if chart is None:return 0,None,stats
    origin,basis=chart
    d=len(basis); groups=[]; buckets={}
    for c in clauses:
        rows=[]
        for l in c:
            a=1<<(abs(l)-1)
            rows.append((_image(a,basis),int(l<0)^dot(a,origin)))
        eq=canonical(d,rows)
        if eq is None:stats["discarded_events"]+=1
        elif not eq:return 0,None,stats
        elif group_equal:buckets.setdefault(tuple(a for a,_ in eq),{})[eq]=None
        else:groups.append((eq,))
    groups.extend(tuple(bucket) for bucket in buckets.values())
    identity=tuple(1<<i for i in range(d))
    limit=min(d,sum(len(g).bit_length() for g in groups),cap if cap is not None else d)
    for budget in range(limit+1):
        result=_search(identity,groups,set(),budget,stats,prune)
        if result is not None:break
    else:
        stats["lower_bound"]=limit+1
        return None,None,stats
    kernel,complement,ignored=result
    stats.update(optimum=budget,codimension=len(complement),exceptions=len(ignored),
                 exception_cost=sum(len(groups[i]).bit_length() for i in ignored))
    total=0; witness=None; q=len(kernel)
    for beta in range(1<<len(complement)):
        stats['cosets']+=1
        fixed=_combination(complement,beta)
        forced={}; bad=[]; blocked=False
        for group in groups:
            residual=[]
            for event in group:
                local={}
                if not all(insert(_image(a,kernel),b^dot(a,fixed),local) for a,b in event):continue
                if not local:blocked=True;break
                if len(local)==1:
                    a,b=next(iter(local.values()))
                    if not insert(a,b^1,forced):blocked=True;break
                else:residual.append(tuple(local.values()))
            if blocked:break
            if residual:bad.append(residual)
        if blocked:continue
        value=_avoid(q,forced,bad)
        total+=value
        if value and witness is None:
            prefix=forced.copy(); word=0
            for i in range(q):
                left_basis=prefix.copy()
                left=_avoid(q,left_basis,bad) if insert(1<<i,0,left_basis) else 0
                if left:
                    prefix=left_basis;value=left
                else:
                    if not insert(1<<i,1,prefix):
                        raise ArithmeticError("positive fiber lost both branches")
                    word|=1<<i
            seed=fixed^_combination(kernel,word)
            witness=origin^_combination(basis,seed)
    if witness is not None:
        assert all(any(bool(witness>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
        assert all(dot(witness,a)==b for a,b in xor_rows)
    return total,witness,stats
