"""Two-sided, finite-field observable search with contiguous permutation-pass clusters."""
from math import isqrt
from gram_pass_rail import prepare_passes
from finite_pass_rail import _independent_indices
from commuting_toggle_rails import compose


def _insert(vec,basis,p):
    for i,x in enumerate(vec):
        if not x:
            continue
        if i not in basis:
            inv=pow(x,-1,p)
            basis[i]=[(z*inv)%p for z in vec]
            return
        other=basis[i]
        for j in range(i,len(vec)):
            vec[j]=(vec[j]-x*other[j])%p


def _prefix_levels(order,ident,directions,local,groups,p,cap):
    levels=[[[(ident,)*len(g)] for g in groups]]
    peak=1
    for v in order:
        level=[]
        for g,previous in zip(groups,levels[-1]):
            candidates={}
            for tensor in previous:
                for b in (0,1):
                    new=[]
                    for j,part in zip(g,tensor):
                        step=local[j].get(v,(ident,ident))[b]
                        new.append(compose(step,part) if directions[j] else compose(part,step))
                    candidates[tuple(new)]=None
            ts=list(candidates)
            inds=_independent_indices(ts,len(ident),p,cap)
            level.append([ts[j] for j in inds])
            peak=max(peak,len(inds))
        levels.append(level)
    return levels,peak


def _observable_pivots(suffixes,level,groups,directions,ident,closing,p,start,trace,cap):
    m=len(suffixes); d=len(ident)
    # choices[j][a][u] is the completed cluster permutation for prefix-basis
    # choice a and suffix candidate u. All original pass boundaries are respected.
    choices=[]
    for g,basis in zip(groups,level):
        switches=[]
        for prefix in basis:
            batch=[]
            for suffix in suffixes:
                perm=ident
                for j,part in zip(g,prefix):
                    full=compose(suffix[j],part) if directions[j] else compose(part,suffix[j])
                    perm=compose(full,perm)
                batch.append(perm)
            switches.append(batch)
        choices.append(switches)
    observed={}
    starts=(None,) if trace else (range(d) if start is None else (start,))
    for s in starts:
        origins=tuple(range(d)) if trace else (s,)
        stride=len(origins)*d
        initial=[0]*(m*stride)
        for u in range(m):
            for i,orig in enumerate(origins):
                initial[u*stride+i*d+orig]=1
        reach=[initial]
        for switches in choices:
            nxt={}
            for row in reach:
                for batch in switches:
                    vec=[0]*len(row)
                    for u,perm in enumerate(batch):
                        for i in range(len(origins)):
                            offset=u*stride+i*d
                            for x,y in enumerate(perm):
                                vec[offset+y]=row[offset+x]
                    _insert(vec,nxt,p)
            reach=list(nxt.values())
        for row in reach:
            result=[]
            for u in range(m):
                v=sum(row[u*stride+i*d+x] for i,orig in enumerate(origins)
                      for x in range(d) if closing[x]==orig)
                result.append(v%p)
            _insert(result,observed,p)
            if cap is not None and len(observed)>cap:
                raise ValueError("suffix observable rank exceeds budget")
    return sorted(observed)


def decide_clusters(n,size,passes,order,cluster_sizes,*,prime=2,start=None,
                    closing=None,promised_trace=False,prefix_limit=None,suffix_limit=None):
    """Return ((control mask, start) or None, peak local prefix rank, peak suffix rank).

    cluster_sizes partition the pass list into contiguous nonempty groups.
    Default accepts any closing start. promised_trace requires that every
    accepting assignment have nonzero fixed-point count modulo prime.
    """
    if not isinstance(prime,int) or prime<2 or any(prime%v==0 for v in range(2,isqrt(prime)+1)):
        raise ValueError("prime field required")
    if start is not None and (not isinstance(start,int) or not 0<=start<size or promised_trace):
        raise ValueError("invalid start or simultaneous trace request")
    order,ident,directions,local=prepare_passes(n,size,passes,order)
    closing=ident if closing is None else tuple(closing)
    if sorted(closing)!=list(ident):
        raise ValueError("invalid closing permutation")
    groups=[]; offset=0
    for length in cluster_sizes:
        if not isinstance(length,int) or length<1:
            raise ValueError("nonempty clusters required")
        groups.append(range(offset,offset+length));offset+=length
    if offset!=len(local):
        raise ValueError("clusters must partition all passes")
    if prefix_limit is not None and prefix_limit<1:
        raise ValueError("prefix rank budget below one")
    levels,peak=_prefix_levels(order,ident,directions,local,groups,prime,prefix_limit)
    candidates={(ident,)*len(local):0};suffix_peak=0
    for i in range(n,-1,-1):
        ts=list(candidates)
        inds=_observable_pivots(ts,levels[i],groups,directions,ident,closing,prime,start,promised_trace,suffix_limit)
        reps={ts[j]:candidates[ts[j]] for j in inds}
        suffix_peak=max(suffix_peak,len(reps))
        if not reps:
            return None,peak,suffix_peak
        if not i:
            break
        v=order[i-1]
        candidates={}
        for suffix,mask in reps.items():
            for b in (0,1):
                parts=[]
                for j,part in enumerate(suffix):
                    step=local[j].get(v,(ident,ident))[b]
                    parts.append(compose(part,step) if directions[j] else compose(step,part))
                candidates.setdefault(tuple(parts),mask | (b<<(v-1)))
    for t,mask in reps.items():
        perm=ident
        for part in t:
            perm=compose(part,perm)
        for s in (range(size) if start is None else (start,)):
            if closing[perm[s]]==s:
                return (mask,s),peak,suffix_peak
    raise AssertionError("root observable has no accepting representative")
