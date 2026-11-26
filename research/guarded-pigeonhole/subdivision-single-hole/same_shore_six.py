"""Exact six-terminal disk decision; parallel internal edges are permitted."""
from itertools import permutations
from collections import Counter
import networkx as nx
from matching_multipole import shape,certified_disk_order,local_valid,extend_matching


def classify(graph,ports,colors,order):
    shore=shape(graph,ports)
    if len(ports)!=6 or len({shore[v] for v in ports})!=1 or not nx.is_connected(graph):
        raise ValueError('expected connected same-shore six-pole')
    if not local_valid(graph,ports,colors) or sorted(Counter(colors).values())!=[2,2,2]:
        return False,'local'
    if sorted(order)!=list(range(6)) or not certified_disk_order(graph,ports,order):
        raise ValueError('a certified disk order is required')
    seq=[colors[i] for i in order]
    for base in range(3):
        others=[t for t in seq if t!=base]
        if others[0]==others[2] and others[1]==others[3]:
            H=graph.subgraph(set(graph)-{v for v,c in zip(ports,colors) if c==base})
            M=nx.bipartite.maximum_matching(H,top_nodes={v for v in H if shore[v]})
            if len(M)<len(H):return False,'cross'
            w=extend_matching(graph,ports,colors,base,[(v,M[v]) for v in H if shore[v]])
            assert w is not None
            return True,'cross'
    H=nx.MultiGraph(graph)
    for c in range(3):
        u,v=[v for v,t in zip(ports,colors) if t==c]
        H.add_edge(u,v)
    assert nx.check_planarity(nx.Graph(H))[0]
    return not any(True for _ in nx.bridges(H)),'cap'


if __name__=='__main__':
    from check_matching_multipole import brute_signatures
    n=0
    totals=Counter()
    # A bridged control: glue cube-minus-one-vertex to a square with pendant.
    bridge=nx.cubical_graph()
    terminals=sorted(bridge[0])
    bridge.remove_node(0)
    bridge.add_edges_from([(8,9),(9,10),(10,11),(11,8),(8,12),(terminals[0],10)])
    for g in [*nx.graph_atlas_g(),bridge]:
        if not len(g) or not nx.is_connected(g) or not nx.is_bipartite(g) or max(dict(g.degree()).values())>3:continue
        ports=[v for v in g for _ in range(3-g.degree(v))]
        if len(ports)!=6 or len({shape(g,ports)[v] for v in ports})!=1:continue
        order=next((p for p in permutations(range(6)) if p[0]==0 and certified_disk_order(g,ports,p)),None)
        if order is None:continue
        truth=brute_signatures(g,ports)
        for colors in set(permutations((0,0,1,1,2,2))):
            yes,route=classify(g,ports,colors,order)
            assert yes==(colors in truth)
            totals[route,yes]+=1
        n+=1
    g=nx.Graph()
    for v,neighbors in [(7,(0,1,5)),(8,(0,1,2)),(10,(2,3,4)),(11,(3,4,5))]:
        g.add_edges_from((v,w) for w in neighbors)
    colors=(0,0,1,1,2,2)
    base=[(2,8),(5,7)]
    assert extend_matching(g,list(range(6)),colors,0,base+[(3,10),(4,11)]) is not None
    assert extend_matching(g,list(range(6)),colors,0,base+[(3,11),(4,10)]) is None
    print(n,totals)
