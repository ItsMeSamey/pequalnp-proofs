"""Independent finite checks of the three-port grouped-star reduction."""
from itertools import combinations, product
from random import Random
import networkx as nx

rng = Random(407)

def certificate(g, assignment, ports):
    """Return the same-color connectivity partition on ports and free components."""
    same = nx.Graph()
    same.add_nodes_from(g)
    same.add_edges_from((x,y) for x,y in g.edges if assignment[x] == assignment[y])
    blocks = list(nx.connected_components(same))
    return {tuple(sorted(b & set(ports))) for b in blocks if b & set(ports)}, any(not (b & set(ports)) for b in blocks)

count = 0
for t in range(1,4):
    ports = tuple(range(t))
    for _ in range(15):
        g = nx.Graph()
        g.add_nodes_from(ports)
        start=t
        for size in [2,1]:
            private=list(range(start,start+size))
            start+=size
            g.add_nodes_from(private)
            g.add_edges_from(zip(private,private[1:]))
            for p in ports:
                g.add_edge(p,rng.choice(private))
        for colors in product(range(3), repeat=start):
            old, sealed = certificate(g, colors, ports)
            if sealed:
                continue
            counts={c:sum(colors[p]==c for p in ports) for c in set(colors[:t])}
            target=max(counts, key=counts.get)
            fresh=list(colors[:t])+[target]*(start-t)
            new, sealed=certificate(g, fresh, ports)
            assert not sealed
            assert all(any(set(old_block) <= set(new_block) for new_block in new) for old_block in old)
            count+=1

# Disc model with an exterior vertex adjacent to the entire society in boundary order.
# Include every possible group and port edge in each triangle; contract auxiliary
# edges to simulate adhesion vertices persisting or coinciding with a society point.
embeddings=0
for length in range(3,31):
    graph=nx.Graph()
    ws=[('w',i) for i in range(length)]
    ns=[('n',i) for i in range(length+1)]
    graph.add_edges_from(zip(ws,ws[1:]+ws[:1]))
    graph.add_edges_from((('exterior',),w) for w in ws)
    for i,w in enumerate(ws):
        tri=(ns[i],w,ns[i+1])
        graph.add_edges_from(combinations(tri,2))
        for j in range(1,4):
            for ix,subset in enumerate(combinations(tri,j)):
                graph.add_edges_from(((i,j,ix),p) for p in subset)
    assert nx.check_planarity(graph)[0]
    embeddings+=1
    for i in range(length):
        if i%3==0:
            graph=nx.contracted_nodes(graph,ws[i],ns[i],self_loops=False)
    assert nx.check_planarity(graph)[0]
    embeddings+=1
print(count, "unsealed local colorings and", embeddings, "disc scaffold embeddings passed")
