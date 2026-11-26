from itertools import combinations,permutations,product
import networkx as nx
E=list(combinations(range(4),2))
partitions=set();count=0
for rows in product(permutations((0,1,2)),repeat=4):
    tips=[]
    for u,v in E:
        cu=rows[u][[w for w in range(4) if w!=u].index(v)]
        cv=rows[v][[w for w in range(4) if w!=v].index(u)]
        if cu==cv:break
        tips.append(3-cu-cv)
    if len(tips)!=6:continue
    count+=1
    partitions.add(tuple(sorted(tuple(i for i,c in enumerate(tips) if c==k) for k in range(3))))
def match(S):
    if not S:yield ();return
    i,*r=S
    for j in r:
        for rest in match([k for k in r if k!=j]):yield ((i,j),)+rest
missing=set(match(list(range(6))))-partitions
opposite=tuple((i,j) for i,j in combinations(range(6),2) if set(E[i]).isdisjoint(E[j]))
assert missing=={opposite} and len(partitions)==14
g=nx.Graph()
for i,(u,v) in enumerate(E):g.add_edges_from(((u,4+i),(v,4+i)))
g.add_edges_from((4+i,4+j) for i,j in opposite)
assert nx.is_isomorphic(g,nx.petersen_graph())
print('1296 assignments,',count,'proper, 14 partitions; missing',opposite,'caps to Petersen')
