from itertools import combinations,product
from collections import Counter
import networkx as nx

def check(g, expected):
    edges=sorted(tuple(sorted(e)) for e in g.edges)
    ids={e:i for i,e in enumerate(edges)}
    cols=[0]*len(edges)
    for j,cycle in enumerate(nx.cycle_basis(g)):
        for a,b in zip(cycle,cycle[1:]+cycle[:1]):
            cols[ids[tuple(sorted((a,b)))]] |= 1<<j
    points=set(cols); d=len(edges)-len(g)+1
    assert len(points)==len(edges) and 0 not in points
    maximum=0
    for a,b,c in combinations(points,3):
        if a^b==c: continue
        maximum=max(maximum,len(points & {a,b,c,a^b,a^c,b^c,a^b^c}))
    assert maximum<=5
    lines={tuple(sorted((a,b,a^b))) for a,b in combinations(points,2) if a^b in points}
    for a,b,c in lines:
        sizes=Counter(min(t,t^a,t^b,t^c) for t in points-{a,b,c})
        assert Counter(sizes.values())=={2:3,1:len(edges)-9}
    mask=range(1<<d)
    count=sum(all(((x&p).bit_count()|(y&p).bit_count())&1 for p in points)
              for x,y in product(mask,repeat=2))
    assert count==expected
    print(len(g),len(edges),d,len(lines),maximum,count)

check(nx.cubical_graph(),24)
check(nx.petersen_graph(),0)
