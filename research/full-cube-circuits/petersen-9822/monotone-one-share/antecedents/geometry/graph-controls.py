from itertools import combinations
edges={(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)}
adj=[{w for u,w in edges if u==v}|{u for u,w in edges if w==v} for v in range(10)]
assert len(edges)==13 and max(map(len,adj))==3
assert all(len(adj[u]&adj[v])<2 for u,v in combinations(range(10),2))
mask=next(mask for k in range(11) for mask in combinations(range(10),k) if all(u in mask or v in mask for u,v in edges))
assert len(mask)==6
assigned={v:[] for v in mask}
for u,v in sorted(edges):
 c=u if u in mask else v
 assigned[c].append(v if c==u else u)
print('cover',mask,'star neighborhoods',assigned)
for s in range(1024):
 term=any((s>>u&1) and any(s>>v&1 for v in ns) for u,ns in assigned.items())
 assert term==any((s>>u&1) and (s>>v&1) for u,v in edges)
print('gates',sum(len(n)-1 for n in assigned.values())+len(mask)+len(mask)-1,'assignments',1024)
