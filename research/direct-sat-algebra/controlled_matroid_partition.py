"""Certified rank partition and exact binary controlled-pencil counting."""
from collections import deque
from controlled_image_peeling import specialization
from controlled_witness_radius import ProjectedOracle, column_basis, row_equations
from quadratic_target import affine_domain, apply_basis, insert, parity, reduce_vector


def partition(U,V,force_s=(),force_t=()):
    """Return an optimal partition and a common independent set in the contracted pair."""
    k=len(U)
    s,t=set(force_s),set(force_t)
    ground=set(range(k))
    if len(V)!=k or s&t or not (s|t)<=ground:
        raise ValueError("invalid partition restrictions")
    free=sorted(ground-s-t)
    ub,vb=column_basis(U[i] for i in s),column_basis(V[i] for i in t)
    u={i:reduce_vector(U[i],ub)[0] for i in free}
    v={i:reduce_vector(V[i],vb)[0] for i in free}
    common=set()
    while True:
        ur,vr={},{}
        for i in sorted(common):
            insert(u[i],1<<i,ur)
            insert(v[i],1<<i,vr)
        outside=[i for i in free if i not in common]
        first={i:reduce_vector(u[i],ur) for i in outside}
        second={i:reduce_vector(v[i],vr) for i in outside}
        parent={i:None for i in outside if first[i][0]}
        queue=deque(parent)
        while queue:
            i=queue.popleft()
            if i not in common and second[i][0]:
                while i is not None:
                    common.symmetric_difference_update([i])
                    i=parent[i]
                break
            if i in common:
                neighbors=[j for j in outside if first[j][0] or first[j][1]>>i&1]
            else:
                neighbors=[j for j in sorted(common) if second[i][1]>>j&1]
            for j in neighbors:
                if j not in parent:
                    parent[j]=i
                    queue.append(j)
        else:
            # Unreached columns are U-spanned by unreached common elements.
            # Reached columns are V-spanned by reached common elements.
            s.update(i for i in free if i not in parent)
            t.update(parent)
            ranks=(len(column_basis(U[i] for i in s)),len(column_basis(V[i] for i in t)))
            assert sum(ranks)==len(ub)+len(vb)+len(common)
            return tuple(sorted(s)),tuple(sorted(t)),tuple(sorted(common)),ranks


def exact(m,A,b,U,q,*,force_s=(),force_t=(),budget=None,equations=()):
    """Budget bounds the partition exponent. An uncomputed count is returned as None."""
    A,U,q,equations=tuple(A),tuple(U),tuple(q),tuple(equations)
    n=len(A)
    if m<0 or len(U)!=len(q) or any(not 0<=v<1<<m for v in (*A,b,*U)):
        raise ValueError("invalid output dimensions")
    if any(not 0<=v<1<<n or c not in (0,1) for v,c in q+equations):
        raise ValueError("invalid affine data forms")
    if budget is not None and budget<0:
        raise ValueError("negative budget")
    image=column_basis(U)
    rem=[reduce_vector(z,image)[0] for z in (*A,b)]
    flat=affine_domain(n,list(equations)+row_equations(rem[:-1],rem[-1],m))
    if flat is None:
        return 0,None,{"status":"infeasible-flat"}
    origin,dirs,_=flat
    restricted_A=[apply_basis(A,d) for d in dirs]
    restricted_b=b^apply_basis(A,origin)
    forms=[(sum(parity(v&d)<<j for j,d in enumerate(dirs)),c^parity(v&origin)) for v,c in q]
    V=[v for v,c in forms]
    S,T,I,ranks=partition(U,V,force_s,force_t)
    info=dict(S=S,T=T,common=I,ranks=ranks,status="counted")
    if budget is not None and sum(ranks)>budget:
        info["status"]="budget"
        return None,None,info
    rows={}
    pivots=[V[i] for i in T if insert(V[i],1<<len(rows),rows)]
    coords=[reduce_vector(V[i],rows)[1] for i in T]
    total,witness=0,None
    for mask in range(1<<len(pivots)):
        H=column_basis(U[i] for i,coord in zip(T,coords) if parity(mask&coord)^forms[i][1])
        pins=[(v,(mask>>j)&1) for j,v in enumerate(pivots)]
        oracle=ProjectedOracle(m,restricted_A,restricted_b,[U[i] for i in S],
                               [forms[i] for i in S],H,pins)
        count=oracle.count()
        total+=count<<(len(T)-len(H))
        if count and witness is None:
            y=origin^apply_basis(dirs,oracle.witness_y())
            ways,x=specialization(m,A,b,U,q,y)
            assert ways
            witness=x,y
    return total,witness,info
