from itertools import combinations
import networkx as nx
H=nx.Graph([(3,4),(0,4),(0,5),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)])
V=set(H)
assert nx.is_connected(H) and min(dict(H.degree).values())==2
assert all(len(set(H[u]) & set(H[v]))<=1 for u,v in combinations(V,2))
for v,n in zip(sorted(H),[2,2,1,1,2,2,1,1]):
    h=H.subgraph(V-{v});assert nx.is_connected(h)
    assert sum(all(d==2 for _,d in h.subgraph(S).degree) for S in combinations(h,5))==n
    d=H.degree(v);assert nx.is_isomorphic(H.subgraph(V-{v}-set(H[v])),nx.path_graph(7-d))
cs=[]
for k in range(9):
    for tup in combinations(V,k):
        s=set(tup)
        if all(a in s or b in s for a,b in H.edges) and not any(t<=s for t in cs):cs.append(s)
assert len(cs)==9
print('all eight deletions, path cofactors, C4-free, 10 edges, 9 minimal covers verified')
