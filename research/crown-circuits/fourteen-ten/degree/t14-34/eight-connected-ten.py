"""Reconstruct ten-vertex hosts from one marked branching cut vertex."""
from itertools import combinations, combinations_with_replacement
import networkx as nx


def marked_hosts():
    atlas=[g for g in nx.graph_atlas_g() if 2<=len(g)<=7 and nx.is_connected(g)
           and max(dict(g.degree()).values())<=3]
    by_size={}
    for g in atlas:
        by_size.setdefault((len(g),g.number_of_edges()),[]).append(g)
    shapes=[]
    for degree in (2,3):
        for leaves in range(degree-1):
            for k in range(2,degree-leaves+1):
                for keys in combinations_with_replacement(sorted(by_size), k):
                    if sum(n for n,e in keys)!=9-leaves or sum(e for n,e in keys)!=14-degree:
                        continue
                    from itertools import product
                    for bank in product(*(by_size[key] for key in keys)):
                        body=nx.disjoint_union_all(bank)
                        for links in combinations([v for v,d in body.degree() if d<3],degree-leaves):
                            g=body.copy()
                            g.add_edges_from((9,v) for v in links)
                            g.add_edges_from((9,len(body)+j) for j in range(leaves))
                            if nx.is_connected(g) and not any(nx.is_isomorphic(g,h) for h in shapes):
                                shapes.append(g)
    return shapes


if __name__=='__main__':
    for g in marked_hosts():
        print(nx.to_graph6_bytes(g,header=False).decode().strip(), sorted(dict(g.degree()).values()))
