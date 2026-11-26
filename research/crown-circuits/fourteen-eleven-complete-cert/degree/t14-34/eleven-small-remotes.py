"""Enumerate dense subcubic graphs on eight and nine vertices for small remote shores."""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import networkx as nx

def add_vertex(bank,n,edge_totals):
    groups=defaultdict(list)
    for g in bank:
        v=len(g)
        for k in (1,2,3):
            if g.number_of_edges()+k not in edge_totals:continue
            avail=[a for a,d in g.degree() if d<3]
            for neighbors in combinations(avail,k):
                h=g.copy()
                h.add_edges_from((v,a) for a in neighbors)
                key=(h.number_of_edges(),nx.weisfeiler_lehman_graph_hash(h))
                if not any(nx.is_isomorphic(h,other) for other in groups[key]):
                    groups[key].append(h)
    return [g for graphs in groups.values() for g in graphs]

if __name__=='__main__':
    atlas=[g for g in nx.graph_atlas_g() if len(g)==7 and nx.is_connected(g) and max(dict(g.degree()).values())<=3]
    eight=add_vertex(atlas,8,{10,11,12})
    nine=add_vertex(eight,9,{13})
    prefix=Path(__file__).resolve().parents[2]
    src=(prefix/'geometry/fourteen34/connected-eleven-cuts.py').read_text()
    env={'__file__':str(prefix/'geometry/fourteen34/connected-eleven-cuts.py')}
    exec(src[:src.index('def add(')],env)
    for n,e,bank in [(8,11,eight),(8,12,eight),(9,13,nine)]:
        relevant=[g for g in bank if g.number_of_edges()==e]
        survivors=[nx.to_graph6_bytes(g,header=False).decode().strip() for g in relevant if env['ok'](g)]
        print(n,e,len(relevant),survivors)
