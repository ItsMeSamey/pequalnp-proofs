from itertools import combinations
import networkx as nx
from sweep import ordered_sweep

def extract_faces(embedding):
    darts=set();which={};faces=[]
    for v in embedding:
        for w in embedding[v]:
            if (v,w) in darts:continue
            cyc=embedding.traverse_face(v,w,darts)
            for a,b in zip(cyc,cyc[1:]+cyc[:1]):
                which[a,b]=len(faces)
            faces.append(cyc)
    return faces,which

def prepare(embedding,first,second):
    """Connected simple plane incidence graph, nodes ('h',i) and ('d',j), consecutive star IDs."""
    faces,which=extract_faces(embedding)
    dual=nx.Graph();dual.add_nodes_from(range(len(faces)));interfaces={}
    for v,w in embedding.to_undirected().edges:
        e=frozenset((v,w));i,j=which[v,w],which[w,v]
        if i==j:continue
        ij=tuple(sorted((i,j)))
        interfaces.setdefault(ij,set()).add(e);dual.add_edge(i,j)
    dualpath=nx.shortest_path(dual,first,second)
    seam={next(iter(interfaces[tuple(sorted((i,j)))])) for i,j in zip(dualpath,dualpath[1:])}
    stars=[{w[1]:int(frozenset((('h',i),w)) in seam) for w in embedding[('h',i)]}
           for i in range(sum(v[0]=='h' for v in embedding))]
    taken=set();selected=[]
    for i,j in combinations(range(len(stars)),2):
        for u,v in combinations(sorted(stars[i].keys()&stars[j].keys()),2):
            if stars[i][u]^stars[i][v]^stars[j][u]^stars[j][v]!=1:continue
            hs=(('h',i),('h',j));ds=(('d',u),('d',v));vertices=set(hs+ds)
            if vertices&taken:continue
            edges={frozenset((h,d)) for h in hs for d in ds}
            cutdual=dual.copy()
            cutdual.remove_edges_from(key for key,es in interfaces.items() if es<=edges)
            inside=nx.node_connected_component(cutdual,first)
            assert second not in inside
            selected.append((len(inside),((i,j),(u,v))));taken.update(vertices)
    return stars,[cycle for _,cycle in sorted(selected)]
