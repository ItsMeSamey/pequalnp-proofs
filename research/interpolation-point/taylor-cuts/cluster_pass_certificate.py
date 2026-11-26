"""Actual-assignment certificates of local reachability and observable suffix closure."""
from cluster_pass_rail import _observable_pivots
from finite_pass_rail import _independent_indices
from gram_pass_rail import prepare_passes
from commuting_toggle_rails import compose


def _setup(n,size,passes,order,lengths,start,closing):
    order,identity,directions,local=prepare_passes(n,size,passes,order)
    groups=[]
    offset=0
    for length in lengths:
        if type(length) is not int or length<1:
            raise ValueError("invalid cluster length")
        groups.append(tuple(range(offset,offset+length)))
        offset+=length
    if offset!=len(local):
        raise ValueError("incomplete cluster partition")
    closing=identity if closing is None else tuple(closing)
    if sorted(closing)!=list(identity) or (start is not None and not 0<=start<size):
        raise ValueError("invalid closure")
    return order,identity,directions,local,groups,closing


def _parts(mask,variables,group,identity,directions,local):
    parts=[]
    for j in group:
        p=identity
        for v in variables:
            q=local[j].get(v,(identity,identity))[(mask>>(v-1))&1]
            p=compose(q,p) if directions[j] else compose(p,q)
        parts.append(p)
    return tuple(parts)


def _select(masks,word,pivots,claimed):
    """Producer selects basis masks. Verifier checks actual masks span candidates."""
    if claimed is None:
        return [masks[i] for i in pivots([word(m) for m in masks])] if masks else []
    if not isinstance(claimed,(tuple,list)):
        raise ValueError("expected a representative list")
    combined=list(claimed)+masks
    if combined and any(i>=len(claimed) for i in pivots([word(m) for m in combined])):
        raise ValueError("representatives do not span successors")
    return list(claimed)


def _compute(n,size,passes,order,lengths,start,closing,certificate,checking):
    order,ident,directions,local,groups,closing=_setup(n,size,passes,order,lengths,start,closing)
    if checking:
        prefixes,suffixes=certificate
        if len(prefixes)!=n+1 or len(suffixes)!=n+1:
            raise ValueError("wrong certificate depth")
    else:
        prefixes,suffixes=[],[None]*(n+1)
    levels=[]
    allowed=0
    def validated(masks,allowed):
        if not isinstance(masks,(list,tuple)) or any(type(m)!=int or m<0 or m&~allowed for m in masks):
            raise ValueError("representative outside its partial assignment")
        return masks
    for i in range(n+1):
        if i:
            bit=1<<(order[i-1]-1)
            allowed|=bit
        level=[]
        produced=[]
        if checking and len(prefixes[i])!=len(groups):
            raise ValueError("wrong number of clusters")
        for g,group in enumerate(groups):
            cand=[0] if not i else [m|b for m in prefixes[i-1][g] for b in (0,bit)]
            word=lambda m:_parts(m,order[:i],group,ident,directions,local)
            found=_select(cand,word,lambda ts:_independent_indices(ts,size,2,None),
                          validated(prefixes[i][g],allowed) if checking else None)
            level.append([word(m) for m in found])
            produced.append(found)
        if not checking:
            prefixes.append(produced)
        levels.append(level)
    allowed=0
    for i in range(n,-1,-1):
        if i<n:
            bit=1<<(order[i]-1)
            allowed|=bit
        cand=[0] if i==n else [m|b for m in suffixes[i+1] for b in (0,bit)]
        word=lambda m:_parts(m,order[i:],range(len(local)),ident,directions,local)
        def pivots(ts):
            return _observable_pivots(ts,levels[i],groups,directions,ident,closing,2,start,False,None)
        found=_select(cand,word,pivots,validated(suffixes[i],allowed) if checking else None)
        if not checking:
            suffixes[i]=found
    # Every root representative must vanish on each required diagonal separately.
    for mask in suffixes[0]:
        p=ident
        for q in _parts(mask,order,range(len(local)),ident,directions,local):
            p=compose(q,p)
        for s in (range(size) if start is None else (start,)):
            if closing[p[s]]==s:
                return ("sat",mask,s) if not checking else False
    return True if checking else ("unsat",prefixes,suffixes)


def produce(n,size,passes,order,lengths,*,start=None,closing=None):
    return _compute(n,size,passes,order,lengths,start,closing,None,False)


def verify(n,size,passes,order,lengths,certificate,*,start=None,closing=None):
    """Verify over F2. SAT checks original gates. UNSAT checks both span inductions."""
    try:
        kind,*data=certificate
        if kind=="sat":
            mask,s=data
            passes=[(forward,tuple((lit,tuple(p),tuple(q)) for lit,p,q in gates)) for forward,gates in passes]
            *_,closing=_setup(n,size,passes,order,lengths,start,closing)
            if type(mask)!=int or mask<0 or mask.bit_length()>n or type(s)!=int or not 0<=s<size or (start is not None and s!=start):
                return False
            state=s
            for _,gates in passes:
                for lit,p,q in gates:
                    bit=((mask>>(abs(lit)-1))&1)^(lit<0)
                    state=(q if bit else p)[state]
            return closing[state]==s
        if kind=="unsat":
            return _compute(n,size,passes,order,lengths,start,closing,data,True)
    except (TypeError,ValueError,IndexError):
        return False
    return False
