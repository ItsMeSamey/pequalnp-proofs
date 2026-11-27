from itertools import combinations
import random
import networkx as nx
from check import brute
from plane import prepare,extract_faces
from sweep import ordered_sweep
rng=random.Random(771);yes=no=0;mx=0
for n in (1,2,3):
    g=nx.Graph()
    for i in range(n):
        for j in (0,1):
            h=('h',2*i+j)
            for d in [2*i,2*i+1,2*n+i+j]:g.add_edge(h,('d',d))
        if i%2:
            for d in [2*i,2*n+i+1]:g.add_edge(('h',2*n+i//2),('d',d))
    planar,emb=nx.check_planarity(g);assert planar
    faces,_=extract_faces(emb)
    for first,second in combinations(range(len(faces)),2):
        stars,cycles=prepare(emb,first,second);mx=max(mx,len(cycles))
        for _ in range(4):
            s,t=rng.sample([v[1] for v in g if v[0]=='d'],2)
            val=ordered_sweep(stars,s,t,cycles)
            assert val==brute(stars,s,t)
            if val:yes+=1
            else:no+=1
print('end-to-end embedding',yes,no,'maximum selected',mx)
