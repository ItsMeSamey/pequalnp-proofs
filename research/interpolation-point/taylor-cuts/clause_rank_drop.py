"""Arity-independent common rank-one restriction for counting CNF with XOR pins."""
from affine_cell_energy import dot,solve
from affine_cover_solver import insert


def _image(mask,directions):
    return sum(dot(mask,d)<<i for i,d in enumerate(directions))


def _combination(vectors,word):
    summed=0
    for i,v in enumerate(vectors):
        if word>>i&1:
            summed^=v
    return summed


def _basis(vectors):
    pivots={}
    result=[]
    for a in vectors:
        k=len(pivots)
        insert(a,0,pivots)
        if len(pivots)>k:
            result.append(a)
    return result


def _restrict(kernel, normals):
    """Return a nullspace basis and a complementary basis in original coordinates."""
    constraints = [(a, 0) for a in normals]
    _, small = solve(len(kernel), constraints)
    complement = []
    for j, a in enumerate(normals):
        constraints[j] = (a, 1)
        unit, _ = solve(len(kernel), constraints)
        complement.append(_combination(kernel, unit))
        constraints[j] = (a, 0)
    return tuple(_combination(kernel, v) for v in small), complement


def _obstruction(kernel, events):
    for event in events:
        projected = _basis(_image(a, kernel) for a, _ in event)
        if len(projected) > 1:
            return projected
    return []


def _optimal(kernel, events, budget, stats):
    stats["search_nodes"] += 1
    rows = _obstruction(kernel, events)
    if not rows:
        return kernel, [], []
    r = len(rows)
    if r - 1 > budget:
        return None
    for mask in range(1, 1 << r):
        pivot = mask.bit_length() - 1
        normals = [a ^ (rows[pivot] if mask >> j & 1 else 0)
                   for j, a in enumerate(rows) if j != pivot]
        small, complement = _restrict(kernel, normals)
        child = _optimal(small, events, budget - r + 1, stats)
        if child is not None:
            final, more, ranks = child
            return final, complement + more, [r] + ranks
    return None


def count(n,clauses,xor_rows=(),*,cap=None,optimal=False):
    """Return (count,witness,metrics); count=None denotes a codimension cap miss."""
    if type(n) is not int or n<0 or cap is not None and (type(cap) is not int or cap<0):
        raise ValueError("invalid dimension or budget")
    clauses=[tuple(c) for c in clauses]
    if any(type(l) is not int or not 1<=abs(l)<=n for c in clauses for l in c):
        raise ValueError("invalid literal")
    xor_rows=tuple(xor_rows)
    domain=solve(n,xor_rows)
    stats={"discarded_events":0,"ranks":[],"codimension":0,"lower_bound":0,"cosets":0}
    if domain is None:
        return 0,None,stats
    origin,chart=domain
    d=len(chart)
    events=[]
    for clause in clauses:
        basis={}
        for lit in clause:
            mask=1<<(abs(lit)-1)
            if not insert(_image(mask,chart),int(lit<0)^dot(mask,origin),basis):
                stats["discarded_events"]+=1
                break
        else:
            if not basis:
                return 0,None,stats
            events.append(tuple(basis.values()))
    kernel=tuple(1<<i for i in range(d))
    complements=[]
    if optimal:
        stats["search_nodes"] = 0
        limit = d if cap is None else min(d, cap)
        for budget in range(limit + 1):
            solution = _optimal(kernel, events, budget, stats)
            if solution is not None:
                kernel, complements, stats["ranks"] = solution
                stats["codimension"] = stats["lower_bound"] = len(complements)
                break
        else:
            stats["lower_bound"] = limit + 1
            return None, None, stats
    else:
        while projected := _obstruction(kernel, events):
            r = len(projected)
            stats["ranks"].append(r)
            stats["codimension"] += r
            stats["lower_bound"] += r - 1
            if cap is not None and stats["codimension"] > cap:
                return None, None, stats
            kernel, more = _restrict(kernel, projected)
            complements.extend(more)
    total=0; witness=None
    for bits in range(1<<len(complements)):
        stats["cosets"]+=1
        seed=_combination(complements,bits)
        keep=[]
        for event in events:
            residual={}
            if not all(insert(_image(a,kernel),b^dot(a,seed),residual) for a,b in event):
                continue
            if not residual:
                break
            assert len(residual)==1
            a,b=next(iter(residual.values()))
            keep.append((a,b^1))
        else:
            lift=solve(len(kernel),keep)
            if lift is not None:
                first,free=lift
                total+=1<<len(free)
                if witness is None:
                    internal=seed^_combination(kernel,first)
                    witness=origin^_combination(chart,internal)
    return total,witness,stats
