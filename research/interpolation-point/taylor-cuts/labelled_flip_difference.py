"""Finite-difference search on certified hereditary flip-connected matching hosts."""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations,product

import networkx as nx


def check_order(G,order):
    if len(order)==2 and all(isinstance(side,(list,tuple)) for side in order):
        left,right=map(tuple,order)
        if sorted(left+right)!=sorted(G):
            return False
        L=set(left)
        if any((u in L)==(v in L) for u,v in G.edges):
            return False
        return all(not (G.has_edge(u,y) and G.has_edge(v,x)) or (G.has_edge(u,x) and G.has_edge(v,y))
                   for u,v in combinations(left,2) for x,y in combinations(right,2))
    if sorted(order)!=sorted(G):
        return False
    return all(not (G.has_edge(u,x) and G.has_edge(u,y) and G.has_edge(v,x)) or G.has_edge(v,y)
               for u,v in combinations(order,2) for x,y in combinations(order,2)
               if len({u,v,x,y})==4)


def odd_chord_host(G):
    """Small-host exhaustive recognizer."""
    def extend(path,used):
        for v in G[path[-1]]:
            if v==path[0] and len(path)>=6 and len(path)%2==0 and path[1]<path[-1]:
                size=len(path)
                if not any(G.has_edge(path[i],path[j]) for i in range(size)
                           for j in range(i+3,size,2) if j-i!=size-1):
                    return False
            if v>path[0] and v not in used and not extend(path+[v],used|{v}):
                return False
        return True
    return all(extend([u],{u}) for u in G)


def solve(n,edges,target,**kwargs):
    target=tuple(target)
    if any(x not in (0,1,2) for x in target):
        raise ValueError('invalid target')
    P=tuple(int(g==target) for g in product(range(3),repeat=len(target)))
    return find_nonzero(n,edges,len(target),P,**kwargs)


def find_nonzero(n,edges,b,P,*,strong_order=None,odd_chord=False,connectivity_certificate=None,state_cap=None,
                 primitive=False,cycle_cap=None):
    """P is a trit table in lexicographic order. The callback certifies hereditary connectivity."""
    P=tuple(P)
    edges=tuple((u,v,tuple(g)) for u,v,g in edges)
    if n<0 or b<0 or len(P)!=3**b or any(x not in (0,1,2) for x in P) or any(
            not (0<=u<n and 0<=v<n and u!=v and len(g)==b and all(x in (0,1,2) for x in g))
            for u,v,g in edges) or state_cap is not None and state_cap<0:
        raise ValueError('invalid graph, function table or cap')
    domain=tuple(product(range(3),repeat=b))
    index={g:i for i,g in enumerate(domain)}
    graph=nx.Graph()
    graph.add_nodes_from(range(n))
    groups=defaultdict(list)
    for i,(u,v,g) in enumerate(edges):
        graph.add_edge(u,v)
        groups[tuple(sorted((u,v)))].append(i)
    masks=[(1<<u)|(1<<v) for u,v,g in edges]
    stats=dict(states=0,queries=0,certified=False)
    if cycle_cap is not None and (not primitive or type(cycle_cap) is not int or cycle_cap<0):
        raise ValueError('cycle_cap requires primitive enumeration and a nonnegative integer')
    @lru_cache(None)
    def primitive_flips():
        from primitive_flip_catalogue import build
        templates,metrics=build(n,edges,cycle_cap=cycle_cap)
        stats['catalogue']=metrics
        return templates
    @lru_cache(None)
    def certified():
        if primitive:
            stats['certified']=primitive_flips() is not None
            return stats['certified']
        ok=(strong_order is not None and check_order(graph,strong_order)
            or connectivity_certificate is not None and connectivity_certificate(graph)
            or odd_chord and odd_chord_host(graph))
        stats['certified']=bool(ok)
        return bool(ok)
    @lru_cache(None)
    def match(mask):
        verts=[v for v in graph if mask>>v&1]
        m=nx.max_weight_matching(graph.subgraph(verts),maxcardinality=True)
        if 2*len(m)!=len(verts):
            return None
        return tuple(groups[tuple(sorted(pair))][0] for pair in m)
    def gain(ids):
        return tuple(sum(edges[i][2][j] for i in ids)%3 for j in range(b))
    @lru_cache(None)
    def flips():
        if primitive:
            return primitive_flips()
        out=[]
        for group in groups.values():
            for i,j in combinations(group,2):
                out.append((masks[i],(i,),(j,)))
        buckets=defaultdict(list)
        for p,q in combinations(groups,2):
            if set(p).isdisjoint(q):
                buckets[tuple(sorted(p+q))].append((p,q))
        for alternatives in buckets.values():
            for (p,q),(r,s) in combinations(alternatives,2):
                for i,j,k,l in product(groups[p],groups[q],groups[r],groups[s]):
                    out.append((masks[i]|masks[j],(i,j),(k,l)))
        return out
    @lru_cache(None)
    def translate(h):
        return tuple(index[tuple((x+y)%3 for x,y in zip(g,h))] for g in domain)
    @lru_cache(None)
    def search(mask,table):
        if not any(table):
            return 'UNSAT',None
        if state_cap is not None and stats['states']>=state_cap:
            return 'UNKNOWN',None
        stats['states']+=1
        witness=match(mask)
        if witness is None:
            return 'UNSAT',None
        if table[index[gain(witness)]]:
            return 'SAT',witness
        if not certified():
            return 'UNKNOWN',None
        pending=False
        for used,left,right in flips():
            if mask & used != used:
                continue
            a,c=translate(gain(left)),translate(gain(right))
            derivative=tuple((table[i]-table[j])%3 for i,j in zip(a,c))
            if not any(derivative):
                continue
            stats['queries']+=1
            status,rest=search(mask^used,derivative)
            if status=='UNKNOWN':
                pending=True
            if status=='SAT':
                trial=rest+left
                witness=trial if table[index[gain(trial)]] else rest+right
                return 'SAT',witness
        return ('UNKNOWN' if pending else 'UNSAT'),None
    status,ids=search((1<<n)-1,P)
    if status=='SAT' and (sorted(v for i in ids for v in edges[i][:2])!=list(range(n)) or not P[index[gain(ids)]]):
        raise ArithmeticError('original-ID witness failed replay')
    return status,ids,stats
