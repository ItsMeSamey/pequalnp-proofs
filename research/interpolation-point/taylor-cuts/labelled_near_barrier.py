"""GF(3)-labelled perfect matching near a supplied Tutte barrier."""
from functools import lru_cache
from itertools import combinations

import networkx as nx
from ternary_vector_routes import solve as vector_solve


def solve(n,edges,target,barrier,*,slack_cap=None,component_cap=None,portal_cap=None):
    """n counts vertices. Return (status, source edge IDs or None, metrics)."""
    edges=tuple((u,v,tuple(g)) for u,v,g in edges)
    target=tuple(target)
    B=frozenset(barrier)
    V=frozenset(range(n))
    caps=(slack_cap,component_cap,portal_cap)
    if n<0 or not B<=V or any(c is not None and (type(c) is not int or c<0) for c in caps):
        raise ValueError('invalid graph size, cap or barrier')
    if any(x not in (0,1,2) for x in target) or any(
        u not in V or v not in V or u==v or len(g)!=len(target) or any(x not in (0,1,2) for x in g)
        for u,v,g in edges):
        raise ValueError('invalid labelled edge')
    graph=nx.Graph()
    graph.add_nodes_from(V-B)
    graph.add_edges_from((u,v) for u,v,g in edges if u not in B and v not in B)
    parts=tuple(frozenset(p) for p in nx.connected_components(graph))
    odd={j for j,p in enumerate(parts) if len(p)%2}
    home={v:j for j,p in enumerate(parts) for v in p}
    d=len(B)-len(odd)
    stats=dict(slack=d,port_bound=max(0,3*d//2),patterns=0,vector_calls=0,unknown_calls=0)
    if n%2 or d<0:
        return 'UNSAT',None,stats
    if slack_cap is not None and d>slack_cap or component_cap is not None and any(len(p)>component_cap for p in parts):
        return 'UNKNOWN',None,stats
    zero=(0,)*len(target)
    def plus(a,b):
        return tuple((x+y)%3 for x,y in zip(a,b))
    def combine(first,second):
        out={}
        for a,w in first.items():
            for b,z in second.items():
                out.setdefault(plus(a,b),w+z)
        return out
    tables={}
    neighbors={v:set() for v in V}
    for i,(u,v,g) in enumerate(edges):
        key=tuple(sorted((u,v)))
        tables.setdefault(key,{}).setdefault(g,(i,))
        neighbors[u].add(v)
        neighbors[v].add(u)
    def edge(u,v):
        return tables[tuple(sorted((u,v)))]
    @lru_cache(None)
    def local(mask):
        if not mask:
            return {zero:()}
        u=(mask&-mask).bit_length()-1
        smaller=mask^(1<<u)
        out={}
        for v in neighbors[u]:
            if smaller>>v & 1:
                for g,w in combine(edge(u,v),local(smaller^(1<<v))).items():
                    out.setdefault(g,w)
        return out
    def internal(vertices):
        return local(sum(1<<v for v in vertices))

    def assign(free,used,pairs):
        if not free:
            yield used,pairs
            return
        u=min(free)
        rest=free-{u}
        for v in neighbors[u]:
            if v in rest:
                yield from assign(rest-{v},used,pairs+((u,v),))
            elif v not in B and v not in used:
                yield from assign(rest,used|{v},pairs+((u,v),))

    for size in range(min(len(B),stats['port_bound'])+1):
        for special in combinations(sorted(B),size):
            for used,pairs in assign(frozenset(special),frozenset(),()):
                hit={}
                for v in used:
                    hit.setdefault(home[v],set()).add(v)
                if any((len(vs)%2 != int(j in odd)) or (j in odd and len(vs)<3) for j,vs in hit.items()):
                    continue
                normal=sorted(odd-set(hit))
                ports=sorted(B-set(special))
                if len(normal)!=len(ports):
                    continue
                stats['patterns']+=1
                fixed={zero:()}
                for u,v in pairs:
                    fixed=combine(fixed,edge(u,v))
                for j,p in enumerate(parts):
                    if j not in odd or j in hit:
                        fixed=combine(fixed,internal(p-hit.get(j,set())))
                        if not fixed:
                            break
                if not fixed:
                    continue
                macro=[]
                traces=[]
                for a,u in enumerate(ports):
                    for k,j in enumerate(normal):
                        choices={}
                        for v in parts[j]&neighbors[u]:
                            for g,w in combine(edge(u,v),internal(parts[j]-{v})).items():
                                choices.setdefault(g,w)
                        for g,w in choices.items():
                            macro.append((a,len(ports)+k,g))
                            traces.append(w)
                for g,w in fixed.items():
                    need=tuple((t-x)%3 for t,x in zip(target,g))
                    stats['vector_calls']+=1
                    status,ids,_=vector_solve(2*len(ports),macro,need,portal_cap=portal_cap)
                    if status=='UNKNOWN':
                        stats['unknown_calls']+=1
                    if status=='SAT':
                        witness=w+tuple(i for j in ids for i in traces[j])
                        if sorted(v for i in witness for v in edges[i][:2])!=list(range(n)) or tuple(
                            sum(edges[i][2][j] for i in witness)%3 for j in range(len(target)))!=target:
                            raise ArithmeticError('matching replay failed')
                        return 'SAT',witness,stats
    return ('UNKNOWN' if stats['unknown_calls'] else 'UNSAT'),None,stats
