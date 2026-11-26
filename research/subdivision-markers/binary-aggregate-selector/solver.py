"""Find two linear functionals whose unequal-offset columns span a binary space."""
from collections import deque
from itertools import product
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1]/'unseeded-root-states'))
from solve import canonical, eliminate, functional, image, solve

def basis(cols):
    piv,_=eliminate(cols)
    return [coeff.bit_length()-1 for _,coeff in piv.values()]

def reducer(cols):
    piv,_=eliminate(cols)
    rows=sorted(((i,v) for i,(v,_) in piv.items()),reverse=True)
    def reduce(v):
        for i,row in rows:
            if v>>i&1:
                v^=row
        return v
    return reduce

def apply(h,x):
    return ((h[0]&x).bit_count()&1)+2*((h[1]&x).bit_count()&1)

def interpolate(cols,values):
    return tuple(functional(cols,sum(((v>>j)&1)<<i for i,v in enumerate(values))) for j in range(2))

def common(cols,quot,rank):
    """Unweighted matroid intersection on two copies of each physical element."""
    n=len(cols)
    shift=max((x.bit_length() for x in quot),default=0)
    left=tuple(cols)+tuple(cols)
    right=tuple(quot)+tuple(x<<shift for x in quot)
    size=2*n
    I=set()
    while len(I)<rank:
        chosen=sorted(I)
        outside=[j for j in range(size) if j not in I]
        leftcols=tuple(left[j] for j in chosen)
        rightcols=tuple(right[j] for j in chosen)
        ls={y:solve(leftcols,left[y]) for y in outside}
        rs={y:solve(rightcols,right[y]) for y in outside}
        queue=deque(y for y in outside if ls[y] is None)
        parent={y:None for y in queue}
        augment=None
        while queue:
            v=queue.popleft()
            if v not in I:
                if rs[v] is None:
                    augment=v
                    break
                neighbors=[x for j,x in enumerate(chosen) if rs[v]>>j&1]
            else:
                j=chosen.index(v)
                neighbors=[y for y in outside if ls[y] is None or ls[y]>>j&1]
            for y in neighbors:
                if y not in parent:
                    parent[y]=v
                    queue.append(y)
        if augment is None:
            Y=[e for e in range(n) if e in parent and e+n in parent]
            assert len(canonical(cols[e] for e in range(n) if e not in Y))+2*len(canonical(quot[e] for e in Y))<rank
            return None,Y
        while augment is not None:
            I.symmetric_difference_update({augment})
            augment=parent[augment]
    return sorted(I),None

def extend(cols,offsets,pins,values,stats=None):
    """Extend the prescribed two-bit values on an independent pin basis."""
    n=len(cols)
    rank=len(canonical(cols))
    nbits=max((x.bit_length() for x in cols),default=0)
    base_reduce=reducer(pins)
    quotient=[base_reduce(x) for x in cols]
    chosen,Y=common(cols,quotient,rank)
    if stats is not None:
        stats['nodes']=stats.get('nodes',0)+1
    if chosen is not None:
        lanes=[]
        for j in range(2):
            edges=[y%n for y in chosen if y//n==j]
            eq=tuple(pins)+tuple(cols[e] for e in edges)
            bits=tuple((v>>j)&1 for v in values)+tuple(1^((offsets[e]>>j)&1) for e in edges)
            mask=sum(b<<i for i,b in enumerate(bits))
            lane=functional(eq,mask)
            assert lane is not None
            lanes.append(lane)
        return tuple(lanes)
    if stats is not None:
        stats['deficits']=stats.get('deficits',0)+1
    take=set(Y)
    keep=[e for e in range(n) if e not in take]
    other=tuple(cols[e] for e in keep)
    ycols=tuple(cols[e] for e in Y)
    extra=[ycols[i] for i in basis([base_reduce(y) for y in ycols])]
    wcols=tuple(pins)+tuple(extra)
    for more in product(range(4),repeat=len(extra)):
        if stats is not None:
            stats['branches']=stats.get('branches',0)+1
        local=interpolate(wcols,tuple(values)+more)
        active=tuple(cols[e] for e in Y if apply(local,cols[e])!=offsets[e])
        if len(canonical(active+other))<rank:
            continue
        pi=reducer(active)
        reduced=tuple(pi(x) for x in other)
        offsets2=tuple(offsets[e]^apply(local,cols[e]^pi(cols[e])) for e in keep)
        pins2=canonical(pi(x) for x in wcols)
        assert len(pins2)+len(extra)<len(pins)
        values2=tuple(apply(local,p) for p in pins2)
        result=extend(reduced,offsets2,pins2,values2,stats)
        if result is None:
            continue
        lifted=[]
        for i in range(nbits):
            v=1<<i
            reduced_v=pi(v)
            lifted.append(apply(result,reduced_v)^apply(local,v^reduced_v))
        return tuple(sum(((value>>j)&1)<<i for i,value in enumerate(lifted)) for j in range(2))
    return None

def aggregate(D,tags,k,target,stats=None):
    """D columns encode a binary matrix. Each tag is an ordered pair of k-bit columns."""
    D,tags=tuple(D),tuple(tags)
    if len(tags)!=len(D) or not 0<=target<1<<k or any(min(t)<0 or max(t)>=1<<k for t in tags):
        raise ValueError("invalid checksum dimensions")
    _,cycles=eliminate(D)
    cols=tuple(sum(((c>>e)&1)<<i for i,c in enumerate(cycles)) for e in range(len(D)))
    signatures=[]
    for j in range(k):
        signatures.extend(image(cols,sum(((tag[lane]>>j)&1)<<e for e,tag in enumerate(tags))) for lane in range(2))
    pins=canonical(signatures)
    coeffs=tuple(solve(pins,s) for s in signatures)
    for vals in product(range(4),repeat=len(pins)):
        check=0
        for j in range(k):
            a=image(vals,coeffs[2*j])
            b=image(vals,coeffs[2*j+1])
            check|=((a&1)^(b>>1))<<j
        if check!=target:
            continue
        h=extend(cols,(0,)*len(cols),pins,vals,stats)
        if h is not None:
            colors=tuple(apply(h,e) for e in cols)
            return tuple(sum(((v>>j)&1)<<e for e,v in enumerate(colors)) for j in range(2))
    return None
