"""Horn feasibility under parity equations, using small generated least models."""
from dataclasses import dataclass
from itertools import combinations
from affine_cover_solver import insert


def _rules(n,clauses):
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid dimension")
    rules=[]
    for clause in clauses:
        lits=set(clause)
        if any(not isinstance(l,int) or not 1<=abs(l)<=n for l in lits):
            raise ValueError("invalid signed literal")
        if any(-l in lits for l in lits):
            continue
        heads=[l for l in lits if l>0]
        if len(heads)>1:
            raise ValueError("expected a Horn clause")
        body=sum(1<<(-l-1) for l in lits if l<0)
        rules.append((body,1<<(heads[0]-1) if heads else 0))
    return rules


def _closure(rules,seed):
    while True:
        old=seed
        for body,head in rules:
            if body & seed == body:
                if not head:
                    return None
                seed |= head
        if seed==old:
            return seed


def _rows(n,equations):
    basis={}
    consistent=True
    for mask,b in equations:
        if not isinstance(mask,int) or not 0<=mask<1<<n or b not in (0,1):
            raise ValueError("invalid XOR row")
        consistent &= insert(mask,b,basis)
    return tuple(basis.values()) if consistent else None


def _candidates(n,rules,rows,degree):
    for size in range(min(n,degree)+1):
        for variables in combinations(range(n),size):
            model=_closure(rules,sum(1<<i for i in variables))
            if model is not None and all((model&a).bit_count()%2==b for a,b in rows):
                yield model


def solve_horn_xor(n,signed_clauses,xor_rows=()):
    """Return one original satisfying bitmask, or None. Time n^rank times poly(input)."""
    rules=_rules(n,signed_clauses)
    rows=_effective(n,rules,xor_rows)
    if rows is None:
        return None
    return next(_candidates(n,rules,rows,len(rows)),None)


@dataclass(frozen=True)
class PrincipalHull:
    origin: int
    directions: tuple
    forced_zero: int
    forced_one: int
    classes: tuple


def principal_hull(n,signed_clauses):
    """Return the affine hull of Horn models, or None; all fields use bit masks.

    Each direction is one whole free equivalence class, independent of the others
    in the affine hull. The origin is the least actual model.
    """
    return _principal(n,_rules(n,signed_clauses))


def _principal(n,rules):
    base=_closure(rules,0)
    if base is None:
        return None
    zero=0
    grouped={}
    for i in range(n):
        if base>>i&1:
            continue
        model=_closure(rules,1<<i)
        if model is None:
            zero |= 1<<i
        else:
            grouped[model]=grouped.get(model,0) | (1<<i)
    classes=tuple(grouped.values())
    return PrincipalHull(base,classes,zero,base,classes)


def horn_xor_hull(n,signed_clauses,xor_rows=()):
    """Return (actual model, independent direction masks) for the constrained hull."""
    rules=_rules(n,signed_clauses)
    rows=_effective(n,rules,xor_rows)
    if rows is None:
        return None
    basis={}
    origin=None
    directions=[]
    for x in _candidates(n,rules,rows,len(rows)+1):
        if origin is None:
            origin=x
        v=x^origin
        z=v
        while z:
            i=z.bit_length()-1
            if i not in basis:
                basis[i]=z
                directions.append(v)
                break
            z ^= basis[i]
    return None if origin is None else (origin,tuple(directions))


def _effective(n,rules,equations):
    rows=_rows(n,equations)
    if rows is None:
        return None
    hull=_principal(n,rules)
    if hull is None:
        return None
    selected=[]
    projected={}
    for mask,b in rows:
        linear=sum(((mask&v).bit_count()%2)<<j for j,v in enumerate(hull.directions))
        target=b^((mask&hull.origin).bit_count()%2)
        previous=len(projected)
        if not insert(linear,target,projected):
            return None
        if len(projected)>previous:
            selected.append((mask,b))
    return tuple(selected)


def effective_xor_rank(n,signed_clauses,xor_rows=()):
    """Rank on the Horn affine hull, or None when that hull excludes the target."""
    rows=_effective(n,_rules(n,signed_clauses),xor_rows)
    return None if rows is None else len(rows)


def _clauses(n,clauses):
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid dimension")
    out=[]
    for clause in clauses:
        lits=set(clause)
        if any(not isinstance(l,int) or not 1<=abs(l)<=n for l in lits):
            raise ValueError("invalid signed literal")
        if not any(-l in lits for l in lits):
            out.append(tuple(sorted(lits)))
    return tuple(out)


def solve_horn_exceptions(n,horn_clauses,exceptions,xor_rows=()):
    """Find one model by at most (#exceptions + effective XOR rank) seeds."""
    rules=_rules(n,horn_clauses)
    extras=_clauses(n,exceptions)
    rows=_effective(n,rules,xor_rows)
    if rows is None or () in extras:
        return None
    for x in _candidates(n,rules,rows,len(rows)+len(extras)):
        if all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in clause) for clause in extras):
            return x
    return None


def find_renamable_horn_core(n,clauses,budget=0):
    """Return (flip mask, normalized core, normalized exceptions) in original polarity."""
    from affine_projective_layer import _two_sat
    source=_clauses(n,clauses)
    if not isinstance(budget,int) or budget<0:
        raise ValueError("invalid exceptional-clause budget")
    pairs=[]
    for clause in source:
        # The flip bit must equal 1 for an originally positive literal to become negative.
        negative=[2*(abs(l)-1)+int(l>0) for l in clause]
        pairs.append(tuple(combinations(negative,2)))
    for size in range(min(budget,len(source))+1):
        for exception in combinations(range(len(source)),size):
            excluded=set(exception)
            constraints=[c for i,cs in enumerate(pairs) if i not in excluded for c in cs]
            bits=_two_sat(n,constraints)
            if bits is not None:
                flips=sum(int(b)<<i for i,b in enumerate(bits))
                return flips,tuple(c for i,c in enumerate(source) if i not in excluded),tuple(source[i] for i in exception)
    return None


def solve_renamable_horn_xor(n,clauses,xor_rows=(),budget=0):
    """Find a model, or None on infeasibility; raise if the promised core is missing."""
    found=find_renamable_horn_core(n,clauses,budget)
    if found is None:
        raise ValueError("no renamable Horn core within budget")
    flips,core,extras=found
    def rename(clauses):
        return [tuple(-l if flips>>(abs(l)-1)&1 else l for l in c) for c in clauses]
    shifted=[(a,b^((a&flips).bit_count()%2)) for a,b in xor_rows]
    x=solve_horn_exceptions(n,rename(core),rename(extras),shifted)
    return None if x is None else x^flips
