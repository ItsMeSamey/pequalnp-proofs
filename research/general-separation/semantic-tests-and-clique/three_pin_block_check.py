"""Bounded graph-atlas replay of three-pin block reduction with witnesses."""
from itertools import combinations
from collections import Counter
import networkx as nx


def pair(G,required):
    if len(required)<2:return set(required)
    u,v=required
    if not G.has_edge(u,v):return {u,v}
    H=G.copy()
    H.remove_edge(u,v)
    try:return set(nx.shortest_path(H,u,v))
    except nx.NetworkXNoPath:return None


def oracle(G,required):
    free=list(set(G)-required)
    for s in range(1<<len(free)):
        selected=required|{v for i,v in enumerate(free) if s>>i&1}
        if all(sum(w in selected for w in G[v])%2==0 for v in selected):return selected
    return None


def solve(G,P):
    comps=[set(c) for c in nx.connected_components(G) if c&P]
    if len(comps)>1:
        answers=[pair(G.subgraph(c),c&P) for c in comps]
        return ('disconnected',None if None in answers else set().union(*answers))
    G=G.subgraph(comps[0])
    blocks=list(nx.biconnected_components(G))
    for B in blocks:
        if P<=B:return 'one-block oracle',oracle(G.subgraph(B),P)
    tree=nx.Graph()
    cuts=set(nx.articulation_points(G))
    for i,B in enumerate(blocks):
        tree.add_node(('b',i))
        for v in cuts&B:tree.add_edge(('b',i),('v',v))
    homes=[('v',v) if v in cuts else ('b',next(i for i,B in enumerate(blocks) if v in B)) for v in P]
    paths=[set(nx.shortest_path(tree,a,b)) for a,b in combinations(homes,2)]
    middle,=set.intersection(*paths)
    tree.remove_node(middle)
    if middle[0]=='v':
        v=middle[1]
        if v not in P:return 'cut excluded',set(P)
        result={v}
        for group in nx.connected_components(tree):
            side=set().union(*(blocks[i] for c,i in group if c=='b'))
            ans=pair(G.subgraph(side),P&side)
            if ans is None:return 'cut pinned',None
            result|=ans
        return 'cut pinned',result
    B=blocks[middle[1]]
    allowed=B.copy()
    sides=[]
    for group in nx.connected_components(tree):
        v,=(i for c,i in group if c=='v' and i in B)
        side={v}.union(*(blocks[i] for c,i in group if c=='b'))
        distal=(side-B)&P
        if not distal:continue
        w,=distal
        ans=pair(G.subgraph(side),(v,w))
        if ans is None:allowed.remove(v)
        sides.append((v,w,ans))
    core=pair(G.subgraph(allowed),P&B)
    if core is None:return 'central block',None
    result=core.copy()
    for v,w,ans in sides:result|=(ans if v in core else {w})
    return 'central block',result


if __name__=='__main__':
    hist=Counter()
    for G in nx.graph_atlas_g():
        if len(G)<3:continue
        for triple in combinations(G,3):
            pins=set(triple)
            mode,w=solve(G,pins)
            assert (w is None)==(oracle(G,pins) is None)
            if w is not None:assert pins<=w and all(len(set(G[v])&w)%2==0 for v in w)
            hist[mode]+=1
    print(dict(sorted(hist.items())),'total',sum(hist.values()))
