"""Forced-edge affine consistency for ternary-labelled bipartite perfect matching."""
from bipartite_matching_hull import prepare
from ternary_frame import reduce
from ternary_star_elimination import kernel


def _sum_basis(vectors):
    basis={}
    for row in vectors:
        w=reduce(row,basis)
        p=next((j for j,a in enumerate(w) if a),None)
        if p is not None:
            basis[p]=tuple(a*w[p]%3 for a in w)
    return basis


def solve(n,edges,target,*,repeat=True):
    """Return SAT/UNSAT/UNKNOWN, original matched edge IDs, and per-round ranks."""
    target=tuple(target)
    edges=[(a,b,tuple(v)) for a,b,v in edges]
    if n<0 or any(x not in (0,1,2) for x in target):
        raise ValueError("invalid input")
    width=len(target)
    active=list(range(len(edges)))
    stats={"ranks":[],"removed":[]}
    while True:
        whole=prepare(n,[edges[i] for i in active],width)
        if whole is None:
            return "UNSAT",None,stats
        base,origin,full,_=whole
        stats.setdefault("initial_rank",len(full))
        if any(reduce(tuple((a-b)%3 for a,b in zip(target,origin)),full)):
            return "UNSAT",None,stats
        allowed=[]
        incident=[{} for _ in range(n)]
        pending_witness=None
        for i in active:
            a,b,g=edges[i]
            rename={v:j for j,v in enumerate(v for v in range(n) if v not in (a,b))}
            remaining=[j for j in active if edges[j][0] in rename and edges[j][1] in rename]
            sub=prepare(n-2,[(rename[edges[j][0]],rename[edges[j][1]],edges[j][2])
                             for j in remaining],width)
            if sub is None:
                continue
            ids,o,basis,_=sub
            delta=tuple((t-x-y)%3 for t,x,y in zip(target,g,o))
            if any(reduce(delta,basis)):
                continue
            if not any(delta):
                pending_witness=(i,)+tuple(remaining[j] for j in ids)
            allowed.append(i)
            for v in (a,b):
                incident[v]=_sum_basis((*incident[v].values(),*basis.values()))
        annihilators=[w for span in incident for w in kernel(width,span.values())]
        rank=width-len(_sum_basis(annihilators))
        stats["ranks"].append(rank)
        stats["removed"].append(len(active)-len(allowed))
        if origin==target:
            pending_witness=tuple(active[j] for j in base)
        if pending_witness is None:
            rest=prepare(n,[edges[i] for i in allowed],width)
            if rest is None:
                return "UNSAT",None,stats
            ids,o,_,_=rest
            if o==target:
                pending_witness=tuple(allowed[j] for j in ids)
            elif rank==0:
                raise ArithmeticError("zero intersection failed on surviving matching")
        if pending_witness is not None:
            if (sorted(v for i in pending_witness for v in edges[i][:2])!=list(range(n)) or
                any(sum(edges[i][2][j] for i in pending_witness)%3!=t for j,t in enumerate(target))):
                raise ArithmeticError("failed original matching replay")
            return "SAT",pending_witness,stats
        if allowed==active or not repeat:
            return "UNKNOWN",None,stats
        active=allowed
