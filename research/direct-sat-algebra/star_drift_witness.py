"""Construct target witnesses for K-affine drift on stars of maximum degree < |K|."""
from dataclasses import dataclass


@dataclass(frozen=True)
class Result:
    status: str
    values: tuple | None
    center_trials: int = 0


def _solve_square(f,matrix,rhs):
    """Unique solution, or None for a singular square matrix."""
    n=len(matrix)
    a=[row[:]+[b] for row,b in zip(matrix,rhs)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]),None)
        if pivot is None: return None
        a[j],a[pivot]=a[pivot],a[j]
        inv=f.inverse(a[j][j])
        for k in range(j,n+1): a[j][k]=f.mul(a[j][k],inv)
        for i in range(j+1,n):
            factor=a[i][j]
            if factor:
                for k in range(j,n+1): a[i][k] ^= f.mul(factor,a[j][k])
    x=[0]*n
    for j in reversed(range(n)):
        x[j]=a[j][-1]
        for k in range(j+1,n): x[j] ^= f.mul(a[j][k],x[k])
    return x


def solve(field,n,rows,target=None):
    """Row (i,j,c,terms) gives x_i*x_j+c+sum(a*x_k for k,a in terms)."""
    if n<0: raise ValueError("invalid number of vertices")
    rows=[(i,j,c,tuple(terms)) for i,j,c,terms in rows]
    target=(0,)*len(rows) if target is None else tuple(target)
    if len(target)!=len(rows) or any(not 0<=a<field.size for a in target):
        raise ValueError("invalid field target")
    degrees=[0]*n
    seen=set()
    for i,j,c,terms in rows:
        edge=tuple(sorted((i,j)))
        if not (0<=i<n and 0<=j<n and i!=j and edge not in seen and 0<=c<field.size):
            raise ValueError("invalid simple field-product edge")
        if any(not (0<=k<n and 0<=a<field.size) for k,a in terms):
            raise ValueError("invalid affine drift")
        seen.add(edge)
        degrees[i]+=1
        degrees[j]+=1
    groups={}
    for r,(i,j,_,_) in enumerate(rows):
        if degrees[i]>1 and degrees[j]>1: raise ValueError("not a star forest")
        center,leaf=(j,i) if degrees[j]>1 else (i,j)
        groups.setdefault(center,[]).append((r,leaf))
    if max(degrees,default=0)>=field.size:
        return Result("UNKNOWN",None)
    ordered=[(c,r,v) for c,group in groups.items() for r,v in group]
    indices={v:j for j,(_,_,v) in enumerate(ordered)}
    size=len(ordered)
    matrix=[[0]*size for _ in ordered]
    for j,(_,r,_) in enumerate(ordered):
        for v,a in rows[r][3]:
            if v in indices: matrix[j][indices[v]] ^= a
    values=[0]*n  # Isolates may be fixed to zero regardless of their affine terms.
    start=trials=0
    for center,group in groups.items():
        end=start+len(group)
        for candidate in range(len(group)+1):
            trials+=1
            test=[row[:end] for row in matrix[:end]]
            for j in range(start,end): test[j][j] ^= candidate
            if _solve_square(field,test,[0]*end) is not None:
                values[center]=candidate
                for j in range(start,end): matrix[j][j] ^= candidate
                break
        else:
            raise ArithmeticError("all degree-plus-one center trials failed")
        start=end
    rhs=[]
    for _,r,_ in ordered:
        _,_,c,terms=rows[r]
        b=c^target[r]
        for v,a in terms:
            if v not in indices: b ^= field.mul(a,values[v])
        rhs.append(b)
    leafvals=_solve_square(field,matrix,rhs)
    if leafvals is None: raise ArithmeticError("singular final leaf matrix")
    for (_,_,v),a in zip(ordered,leafvals): values[v]=a
    for (i,j,c,terms),b in zip(rows,target):
        y=c^field.mul(values[i],values[j])
        for v,a in terms: y ^= field.mul(a,values[v])
        if y!=b: raise ArithmeticError("target verification failed")
    return Result("SAT",tuple(values),trials)
