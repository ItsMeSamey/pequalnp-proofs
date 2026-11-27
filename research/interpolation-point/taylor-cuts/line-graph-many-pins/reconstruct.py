"""Recognize simple line graphs of multigraphs and recover an edge-ID-indexed root."""
import networkx as nx
from multigraph import solve_multi

def root_from_graph(n, graph_edges):
    g=nx.Graph()
    g.add_nodes_from(range(n))
    g.add_edges_from(graph_edges)
    classes={}
    for v in g:
        key=frozenset({v}.union(g[v]))
        classes.setdefault(key,[]).append(v)
    representatives={members[0]:members for members in classes.values()}
    quotient=g.subgraph(representatives)
    edges=[None]*n
    next_id=0
    for component in nx.connected_components(quotient):
        if len(component)==1:
            rep=next(iter(component))
            root_edges={rep:(next_id,next_id+1)}
            next_id+=2
        else:
            try:
                inv=nx.inverse_line_graph(quotient.subgraph(component))
            except nx.NetworkXError:
                return None
            ids={v:i for i,v in enumerate(inv,start=next_id)}
            next_id+=len(ids)
            root_edges={}
            for x,y in inv.edges:
                common=set(x)&set(y)
                if len(common)!=1: return None
                root_edges[common.pop()] = (ids[x],ids[y])
        if set(root_edges)!=set(component):return None
        for rep,pair in root_edges.items():
            for v in representatives[rep]:edges[v]=pair
    if any(g.has_edge(i,j)!=bool(set(edges[i])&set(edges[j]))
           for i in range(n) for j in range(i)):
        return None
    return next_id,edges

def solve_graph(n, graph_edges, pins):
    result=root_from_graph(n,graph_edges)
    if result is None:raise ValueError('input is outside the multigraph line-graph class')
    return solve_multi(*result,pins)
