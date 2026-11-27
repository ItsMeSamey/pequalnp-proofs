"""Exact labelled general matching by deficiency of a maximum independent set."""
from itertools import combinations

import networkx as nx
from ternary_vector_routes import solve as vector_solve


def transversal(base, omitted, pairs):
    """Choose one endpoint of every retained base pair by implication SCCs."""
    mate={v:u for i,(a,b) in enumerate(base) if i not in omitted for v,u in ((a,b),(b,a))}
    graph=nx.DiGraph()
    graph.add_nodes_from(mate)
    for u,v in pairs:
        if u in mate and v in mate:
            graph.add_edge(u,mate[v])
            graph.add_edge(v,mate[u])
    parts=list(nx.strongly_connected_components(graph))
    dag=nx.condensation(graph,parts)
    order={u:i for i,c in enumerate(nx.topological_sort(dag)) for u in parts[c]}
    if any(order[u]==order[v] for u,v in mate.items()):
        return None
    chosen=frozenset(u for u,v in mate.items() if order[u]>order[v])
    if any(u in chosen and v in chosen for u,v in pairs):
        raise ArithmeticError('invalid independent transversal')
    return chosen


def solve(n,edges,target,*,deficiency_cap=None,portal_cap=None):
    """Return (status, source edge IDs, metrics). n counts original vertices."""
    edges=tuple((u,v,tuple(g)) for u,v,g in edges)
    target=tuple(target)
    if n<0 or any(c is not None and (type(c) is not int or c<0) for c in (deficiency_cap,portal_cap)):
        raise ValueError('invalid size or cap')
    if any(x not in (0,1,2) for x in target) or any(not (0<=u<n and 0<=v<n and u!=v)
            or len(g)!=len(target) or any(x not in (0,1,2) for x in g) for u,v,g in edges):
        raise ValueError('invalid labelled graph')
    labels={}
    for i,(u,v,g) in enumerate(edges):
        labels.setdefault(tuple(sorted((u,v))),{}).setdefault(g,i)
    graph=nx.Graph()
    graph.add_nodes_from(range(n))
    graph.add_edges_from(labels)
    base=sorted(tuple(sorted(pair)) for pair in nx.max_weight_matching(graph,maxcardinality=True))
    stats=dict(deficiency=None,transversals=0,endpoint_matchings=0,vector_calls=0,unknown_calls=0)
    if 2*len(base)!=n:
        return 'UNSAT',None,stats
    limit=len(base) if deficiency_cap is None else min(len(base),deficiency_cap)
    independent=None
    for d in range(limit+1):
        for omitted in combinations(range(len(base)),d):
            stats['transversals']+=1
            independent=transversal(base,set(omitted),labels)
            if independent is not None:
                break
        if independent is not None:
            break
    if independent is None:
        return 'UNKNOWN',None,stats
    stats['deficiency']=d
    stats['independent']=tuple(sorted(independent))
    interior=[pair for pair in labels if not independent.intersection(pair)]
    crossing=[i for options in labels.values() for i in options.values()
              if (edges[i][0] in independent)!=(edges[i][1] in independent)]
    zero=(0,)*len(target)
    for pairs in combinations(interior,d):
        used={v for pair in pairs for v in pair}
        if len(used)!=2*d:
            continue
        stats['endpoint_matchings']+=1
        states={zero:()}
        for pair in pairs:
            nxt={}
            for a,ids in states.items():
                for g,i in labels[pair].items():
                    k=tuple((x+y)%3 for x,y in zip(a,g))
                    nxt.setdefault(k,ids+(i,))
            states=nxt
        vertices=[v for v in range(n) if v not in used]
        position={v:i for i,v in enumerate(vertices)}
        source=[i for i in crossing if edges[i][0] not in used and edges[i][1] not in used]
        residual=[(position[edges[i][0]],position[edges[i][1]],edges[i][2]) for i in source]
        for a,internal_ids in states.items():
            need=tuple((t-x)%3 for t,x in zip(target,a))
            stats['vector_calls']+=1
            status,ids,_=vector_solve(len(vertices),residual,need,portal_cap=portal_cap)
            if status=='UNKNOWN':
                stats['unknown_calls']+=1
            if status=='SAT':
                witness=internal_ids+tuple(source[i] for i in ids)
                if sorted(v for i in witness for v in edges[i][:2])!=list(range(n)) or tuple(
                    sum(edges[i][2][j] for i in witness)%3 for j in range(len(target)))!=target:
                    raise ArithmeticError('invalid original labelled matching')
                return 'SAT',witness,stats
    return ('UNKNOWN' if stats['unknown_calls'] else 'UNSAT'),None,stats
