"""Witness-preserving reachable pure tensors over a prime field."""
from math import isqrt
from gram_pass_rail import prepare_passes
from commuting_toggle_rails import compose


def _independent_indices(tensors, size, prime, limit):
    """Pivot columns of their coordinate evaluation matrix, without constructing it."""
    width=len(tensors)
    basis=[[1]*width]  # the only zero-factor coordinate
    pivots={0:basis[0]}
    for j in range(len(tensors[0])):
        masks={}
        for i,t in enumerate(tensors):
            for source,target in enumerate(t[j]):
                masks.setdefault((source,target),[]).append(i)
        pivots={}
        for coeffs in basis:
            for support in masks.values():
                vec=[0]*width
                for i in support:
                    vec[i]=coeffs[i]
                for i,a in enumerate(vec):
                    if not a:
                        continue
                    if i not in pivots:
                        inv=pow(a,-1,prime)
                        pivots[i]=[(v*inv)%prime for v in vec]
                        break
                    prev=pivots[i]
                    for k in range(i,width):
                        vec[k]=(vec[k]-a*prev[k])%prime
        basis=list(pivots.values())
        # Partial-coordinate ranks cannot decrease: sum over all target entries
        # at one fixed source recreates the old vector because each local matrix
        # is a permutation. A cap here therefore also bounds final candidate rank.
        if limit is not None and len(basis)>limit:
            raise ValueError("reachable rank exceeds budget")
    return sorted(pivots)


def decide_passes(n,size,passes,order,*,prime=2,start=None,closing=None,
                  promised_trace=False,rank_limit=None):
    """Return ((input mask, closing start) or None, peak F_p prefix rank).

    closing is a fixed final state permutation. The default checks every diagonal
    entry; start restricts to one. promised_trace instead assumes each accepting
    assignment has a number of closing states nonzero modulo prime.
    """
    if not isinstance(prime,int) or prime<2 or any(prime%d==0 for d in range(2,isqrt(prime)+1)):
        raise ValueError("prime field required")
    if start is not None and (not isinstance(start,int) or not 0<=start<size):
        raise ValueError("invalid pinned start")
    if start is not None and promised_trace:
        raise ValueError("choose pinned-start or promised-trace mode")
    order,ident,directions,by_pass=prepare_passes(n,size,passes,order)
    closing=ident if closing is None else tuple(closing)
    if sorted(closing)!=list(ident):
        raise ValueError("invalid closing permutation")
    if rank_limit is not None and rank_limit<1:
        raise ValueError("reachable rank exceeds budget")
    reps={(ident,)*len(by_pass):0}
    peak=1
    for v in order:
        candidates={}
        for tensor,mask in reps.items():
            for b in (0,1):
                successor=[]
                for p,forward,local in zip(tensor,directions,by_pass):
                    a=local.get(v,(ident,ident))[b]
                    successor.append(compose(a,p) if forward else compose(p,a))
                candidates.setdefault(tuple(successor),mask | (b<<(v-1)))
        tensors=list(candidates)
        indices=_independent_indices(tensors,size,prime,rank_limit)
        reps={tensors[j]:candidates[tensors[j]] for j in indices}
        peak=max(peak,len(reps))
    for tensor,mask in reps.items():
        perm=ident
        for p in tensor:
            perm=compose(p,perm)
        final=compose(closing,perm)
        if promised_trace and sum(i==j for i,j in enumerate(final))%prime==0:
            continue
        for s in (range(size) if start is None else (start,)):
            if final[s]==s:
                return (mask,s),peak
    return None,peak
