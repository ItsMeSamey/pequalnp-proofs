"""Rooted native rotations with fixed abstract band endpoints."""
from itertools import product
import networkx as nx
from strict_forest_reference import circles, swap

def solve(reference, triples, s, t):
    owner = {w: j for j, tour in enumerate(circles(reference)) for w in tour}
    g = nx.MultiGraph()
    g.add_nodes_from(owner.values())
    for i, (a,b,c) in enumerate(triples):
        if owner[b] != owner[c]:
            return False, None
        g.add_edge(owner[a], owner[b], key=i)
    roots = {owner[s],owner[t]}
    component = nx.node_connected_component(g,owner[s])
    if owner[t] not in component:
        return True, None
    g = g.subgraph(component).copy()
    todo = [v for v in g if v not in roots and g.degree(v)<=1]
    while todo:
        v = todo.pop()
        if v in g and v not in roots and g.degree(v)<=1:
            todo.extend(g[v])
            g.remove_node(v)
    core = sorted({i for v in g if v in roots or g.degree(v)!=2
                   for _,_,i in g.edges(v,keys=True)})
    for values in product((0,1),repeat=len(core)):
        bits = [0]*len(triples)
        for i,x in zip(core,values):
            bits[i]=x
        perm = swap(reference,[(a,(b,c)[x]) for (a,b,c),x in zip(triples,bits)])
        if any(s in w and t in w for w in circles(perm)):
            return True,bits
    return True,None
