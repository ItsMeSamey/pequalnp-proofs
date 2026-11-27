"""GF(3) polynomial nonvanishing on original size-k matching incidence vectors."""
from functools import lru_cache
from itertools import combinations
import networkx as nx


def solve(n,edges,k,poly,*,brute_cap=None,affine_oracle=None):
    """poly maps edge-ID bitmasks to trits. Return (status, original IDs, metrics).

    brute_cap counts complete size-k evaluations in tight fallback across all nodes.
    affine_oracle(n,edges,vertex_mask,k,polynomial) may resolve tight affine leaves.
    """
    edges=tuple(tuple(edge) for edge in edges)
    if n<0 or k<0 or (brute_cap is not None and (type(brute_cap) is not int or brute_cap<0)):
        raise ValueError('invalid size or brute cap')
    endpoints=[]
    bundles={}
    for i,(u,v) in enumerate(edges):
        if not (0<=u<n and 0<=v<n and u!=v):
            raise ValueError('invalid edge')
        endpoints.append((1<<u)|(1<<v))
        bundles.setdefault(tuple(sorted((u,v))),[]).append(i)
    if any(type(mask) is not int or mask<0 or mask.bit_length()>len(edges) for mask in poly):
        raise ValueError('monomial references an absent edge')
    poly={mask:c%3 for mask,c in poly.items() if c%3}
    stats=dict(nodes=0,safe=0,disjoint=0,unsafe=0,brute=0,affine=0)
    @lru_cache(None)
    def active(V):
        return sum(1<<i for i,ends in enumerate(endpoints) if ends&V==ends)
    @lru_cache(None)
    def maximum(V):
        graph=nx.Graph()
        graph.add_nodes_from(u for u in range(n) if V>>u&1)
        graph.add_edges_from((u,v) for u,v in bundles if V>>u&1 and V>>v&1)
        matching=nx.max_weight_matching(graph,maxcardinality=True)
        return tuple(bundles[tuple(sorted(pair))][0] for pair in matching)
    def ev(P,ids):
        chosen=sum(1<<i for i in ids)
        return sum(c for mask,c in P.items() if mask&chosen==mask)%3
    def valid(V,need,ids):
        return (len(ids)==need and all(type(i) is int and 0<=i<len(edges) and endpoints[i]&V==endpoints[i] for i in ids)
                and len({v for i in ids for v in edges[i]})==2*need)
    def candidates(V,need):
        if need==0:
            yield ()
            return
        if len(maximum(V))<need:
            return
        bit=V&-V
        for i,ends in enumerate(endpoints):
            if ends&bit and ends&V==ends:
                for rest in candidates(V^ends,need-1):
                    yield (i,)+rest
        yield from candidates(V^bit,need)
    def search(V,need,P):
        stats['nodes']+=1
        m=maximum(V)
        if len(m)<need or not P:
            return 'UNSAT',None
        base=m[:need]
        if ev(P,base):
            return 'SAT',base
        d=max(mask.bit_count() for mask in P)
        if d==0 or need==0:
            return 'UNSAT',None
        if len(m)==need:
            if d==1 and affine_oracle is not None:
                stats['affine']+=1
                status,w=affine_oracle(n,edges,V,need,P)
                if status=='SAT' and (not valid(V,need,w) or not ev(P,w)):
                    raise ArithmeticError('invalid affine witness')
                if status not in ('SAT','UNSAT','UNKNOWN'):
                    raise ValueError('invalid affine status')
                if status!='UNKNOWN':
                    return status,w
            for ids in candidates(V,need):
                if brute_cap is not None and stats['brute']>=brute_cap:
                    return 'UNKNOWN',None
                stats['brute']+=1
                if ev(P,ids):
                    return 'SAT',ids
            return 'UNSAT',None
        pending=False
        E=active(V)
        for e,f in combinations((i for i in range(len(edges)) if E>>i&1),2):
            outside=V&~(endpoints[e]|endpoints[f])
            keep=active(outside)
            diff={}
            for mask,c in P.items():
                trimmed=mask&keep
                gone=mask^trimmed
                if gone in (1<<e,1<<f):
                    diff[trimmed]=(diff.get(trimmed,0)+(c if gone==1<<e else -c))%3
            diff={mask:c for mask,c in diff.items() if c and mask.bit_count()<=need-1}
            if not diff:
                continue
            if len(maximum(outside))<len(m)-2:
                stats['unsafe']+=1
                continue
            stats['safe']+=1
            if not endpoints[e]&endpoints[f]:
                stats['disjoint']+=1
            status,w=search(outside,need-1,diff)
            if status=='UNKNOWN':
                pending=True
            elif status=='SAT':
                a=(e,)+w
                return 'SAT',a if ev(P,a) else (f,)+w
        return ('UNKNOWN' if pending else 'UNSAT'),None
    V=(1<<n)-1
    status,w=search(V,k,{m:c for m,c in poly.items() if m.bit_count()<=k})
    if status=='SAT' and (not valid(V,k,w) or not ev(poly,w)):
        raise ArithmeticError('invalid original matching')
    return status,w,stats
