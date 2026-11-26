"""Count viable duals exactly via a single sum over quotient subspaces."""
from itertools import combinations
from math import prod
from solver import affine_count, basis, bits, reduce_with_trace


def echelon_subspaces(h):
    """Yield each binary subspace as a highest-pivot reduced echelon basis."""
    for dimension in range(h+1):
        for pivots in combinations(range(h),dimension):
            free=set(range(h)).difference(pivots)
            slots=[(i,k) for i,p in enumerate(pivots) for k in sorted(free) if k<p]
            for entries in range(1<<len(slots)):
                rows=[1<<p for p in pivots]
                for j in bits(entries):
                    i,k=slots[j]
                    rows[i]|=1<<k
                yield tuple(rows)


def remainder(value, rows):
    for row in reversed(rows):
        if value & (1<<(row.bit_length()-1)):
            value ^=row
    return value


def count_duals(rank, labels, ordinary, fillers, t, target=0, root_label=0,
                moments=(), dual_tests=(), s=None):
    """Same input and filling promise as solver.solve; return the number of covectors."""
    ordinary,fillers,moments=list(ordinary),list(fillers),list(moments)
    if rank<0 or labels<0:
        raise ValueError("negative dimension")
    if not moments:
        moments=[0]*labels
    tests=list(dual_tests)+[(t,0)]+([] if s is None else [(s,1)])
    if (len(moments)!=labels or any(not 0<=x<1<<rank for x in moments)
        or any(not 0<=x<1<<rank or b not in (0,1) for x,b in tests)
        or any(not 0<=v<1<<rank or not 0<=l<1<<labels for v,l in ordinary)
        or any(not 0<=x<1<<labels for x in [target,root_label])
        or any(not 0<=i<len(ordinary) for i in fillers)):
        raise ValueError("invalid lifted instance")
    base_count=affine_count(rank,tests)
    if not base_count:
        return 0
    lifted=[v|(l<<rank) for v,l in ordinary]
    W=basis(lifted[i] for i in fillers)
    free=[i for i in range(rank+labels) if i not in W]
    h=len(free)
    def project(x):
        rem=reduce_with_trace(x,W)[0]
        return sum(((rem>>j)&1)<<i for i,j in enumerate(free))
    cols=[(project(x),v) for x,(v,_) in zip(lifted,ordinary)]
    offset=project(t|((target^root_label)<<rank))
    directions=[project(sum(((m>>j)&1)<<(rank+i) for i,m in enumerate(moments))) for j in range(rank)]
    coeff=[0]+[-prod(1-(1<<j) for j in range(1,c)) for c in range(1,h+1)]
    total=base_count
    for rows in echelon_subspaces(h):
        c=h-len(rows)
        if not c:
            continue
        fixed=tests+[(v,1) for v in {v for q,v in cols if remainder(q,rows)}]
        hits=affine_count(rank,fixed)
        if not hits:
            continue
        const=remainder(offset,rows)
        linear=[remainder(vec,rows) for vec in directions]
        for j in range(h):
            w=sum(((a>>j)&1)<<i for i,a in enumerate(linear))
            rhs=(const>>j)&1
            if w or rhs:
                fixed.append((w,rhs))
        total+=coeff[c]*(hits-affine_count(rank,fixed))
    return total
