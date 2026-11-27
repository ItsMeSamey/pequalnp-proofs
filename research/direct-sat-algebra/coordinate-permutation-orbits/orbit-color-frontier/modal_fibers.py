"""Sufficient, physically verified modal projection to supplied bags."""
from itertools import combinations
from math import isqrt
from cycle_syndrome import build,apply_word
from common_neighbor_bags import proposals


def _read(raw):
    D=len(raw.rotation)
    n=(1+isqrt(1+2*D))//2
    if n%2!=1 or D!=2*n*(n-1):raise ValueError("unrecognized canonical size")
    ref=build(n,[])
    if (tuple(raw.rotation),tuple(raw.flip),raw.start)!=(ref.rotation,ref.flip,ref.start):
        raise ValueError("unrecognized canonical permutations or start")
    if type(raw.zero)!=int or raw.zero<0 or raw.zero.bit_length()>D:raise ValueError("invalid pins")
    allowed={(u,v):15^(raw.zero>>(4*i)&15) for i,(u,v) in enumerate(combinations(range(n),2))}
    return n,allowed


def _solve(raw,n,allowed,bags,budget):
    groups=[(i,) for i in range(n)] if bags is None else [tuple(b) for b in bags]
    vertices=[v for bag in groups for v in bag]
    if any(not bag for bag in groups) or any(type(v)!=int or not 0<=v<n for v in vertices):
        raise ValueError("invalid bag")
    if len(set(vertices))!=len(vertices):raise ValueError("repeated vertex")
    omitted=set(range(n))-set(vertices)
    if omitted and not (omitted=={n-1} and all(allowed[v,n-1]==15 for v in range(n-1))):
        raise ValueError("partition omits constrained or nonpadding vertices")
    def mask(u,v):return allowed[min(u,v),max(u,v)]
    if any(not mask(u,v)&1 for bag in groups for u,v in combinations(bag,2)):
        return 'UNKNOWN',None
    base=[]
    for i,j in combinations(range(len(groups)),2):
        A,B=groups[i],groups[j]
        common=15
        for u in A:
            for v in B:common&=mask(u,v)
        s,t=(len(A)+3)//4,(len(B)+3)//4
        for delta in range(4):
            if common>>delta&1:continue
            left=[0]*len(A)
            right=[0]*len(B)
            for p,u in enumerate(A):
                for q,v in enumerate(B):
                    if mask(u,v)>>delta&1:
                        left[p]+=1
                        right[q]+=1
            if max(left)>=t and max(right)>=s and sum(left)>=s*t:
                return 'UNKNOWN',None
        base.append((i,j,common))
    size=len(groups)
    neighbors=[[] for _ in groups]
    for i,j,common in base:
        if common!=15:
            neighbors[i].append((j,common))
            neighbors[j].append((i,common))
    domains=[15]*size
    if size:domains[0]=1
    stack=[(domains,[-1]*size)]
    while stack:
        if budget[0]==0:return 'UNKNOWN',None
        if budget[0] is not None:budget[0]-=1
        domains,colors=stack.pop()
        free=[i for i,c in enumerate(colors) if c<0]
        if free:
            i=min(free,key=lambda v:(domains[v].bit_count(),-len(neighbors[v]),v))
            for c in range(3,-1,-1):
                if not domains[i]>>c&1:continue
                remaining=domains[:]
                for j,common in neighbors[i]:
                    remaining[j]&=sum(1<<b for b in range(4) if common>>(b^c)&1)
                    if not remaining[j]:break
                else:
                    remaining[i]=1<<c
                    assigned=colors[:]
                    assigned[i]=c
                    stack.append((remaining,assigned))
            continue
        physical=[0]*n
        for bag,c in zip(groups,colors):
            for v in bag:physical[v]=c
        return 'SAT',_replay(raw,n,physical)
    return 'UNSAT',None


def _replay(raw,n,colors):
    # At elapsed step i there are 2n-i rotations remaining. Thus every
    # flip lands on vertex -i mod n with final toggle bit i mod 2.
    ops=[]
    for i in range(2*n):
        if colors[(-i)%n]>>(i%2)&1:ops.append('f')
        ops.append('r')
    word=''.join(ops)
    # Raw start was checked in _read. Follow its active sites individually.
    sites=list(range(0,len(raw.rotation),4))
    for op in word:
        perm=raw.flip if op=='f' else raw.rotation
        sites=[perm[x] for x in sites]
    expected={4*i+(colors[u]^colors[v]) for i,(u,v) in enumerate(combinations(range(n),2))}
    if set(sites)!=expected:raise ArithmeticError("raw word failed physical replay")
    pins=raw.zero.to_bytes((len(raw.rotation)+7)//8,'little')
    if any(pins[i//8]>>(i%8)&1 for i in sites):raise ArithmeticError("raw word hit a pin")
    return word


def _budget(limit):
    if limit is not None and (type(limit)!=int or limit<0):raise ValueError("invalid search node budget")
    return [limit]


def solve(raw,bags=None,*,max_assignments=65536):
    """Return (status, word or None). Budget counts popped partial assignments."""
    n,allowed=_read(raw)
    return _solve(raw,n,allowed,bags,_budget(max_assignments))


def solve_auto(raw,*,max_assignments=65536):
    """Try common-neighbor proposals on the forbidden-zero graph with a shared budget."""
    n,allowed=_read(raw)
    budget=_budget(max_assignments)
    candidates=proposals(range(n),[edge for edge,mask in allowed.items() if not mask&1])
    singleton=next(candidates)
    for bags in candidates:
        result=_solve(raw,n,allowed,bags,budget)
        if result[0]!='UNKNOWN' or budget[0]==0:return result
    return _solve(raw,n,allowed,singleton,budget)
