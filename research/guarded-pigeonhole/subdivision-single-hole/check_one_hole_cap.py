from itertools import permutations,product
from collections import Counter
import networkx as nx
rows=(9,10,24,21,22)
N=[[j for j in range(5) if r>>j&1] for r in rows]
G=nx.Graph([(i,5+j) for i,J in enumerate(N) for j in J])
assert nx.is_connected(G) and nx.check_planarity(G)[0] and not list(nx.bridges(G))
supp=G.copy()
for v in [x for x in G if G.degree(x)==2]:
    u,w=list(supp[v]);assert not supp.has_edge(u,w)
    supp.remove_node(v);supp.add_edge(u,w)
assert nx.is_isomorphic(supp,nx.complete_graph(4))
sig=Counter()
for tris in product(list(permutations(range(3))),repeat=5):
    seen=[set() for _ in rows]
    for J,col in zip(N,tris):
        for j,c in zip(J,col):seen[j].add(c)
    if any(len(S)!=(2 if j<3 else 3) for j,S in enumerate(seen)):continue
    sig[tuple(tris[i][2] for i in range(3))+tuple(next(iter({0,1,2}-seen[j])) for j in range(3))]+=1
def key(s):
    if len(set(s))==1:return 'mono'
    if len(set(s))==2:
        minority=next(c for c in set(s) if s.count(c)==2)
        return 'h'+str(i:=s[:3].index(minority))+str(s[3:].index(minority))
    return ''.join(str(s[:3].index(c)) for c in s[3:])
assert all(Counter(s[:3])==Counter(s[3:]) for s in sig)
keys={key(s) for s in sig}
expected={'h'+str(i)+str(j) for i,j in product(range(3),repeat=2)}|{''.join(map(str,x)) for x in permutations(range(3))}
assert keys==expected-{'102'}
print(len(sig),'labeled traces;',sum(sig.values()),'full colorings;',sorted(keys))
