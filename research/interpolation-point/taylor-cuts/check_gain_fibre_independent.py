"""Compare raw colored-fibre automorphisms with direct gain-shift permutations."""
from collections import Counter
from itertools import permutations, product
import networkx as nx
from networkx.algorithms.isomorphism import DiGraphMatcher, categorical_edge_match, categorical_node_match


def check(n,edges,b):
    gains=list(product(range(3),repeat=b))
    zero=gains[0]
    def add(a,c):
        return tuple((x+y)%3 for x,y in zip(a,c))
    def key(u,v,g):
        return (min(u,v),max(u,v),g)
    cells=Counter(key(*e) for e in edges)
    graph=nx.DiGraph()
    for u in range(n):
        graph.add_node((u,None),kind=0)
        for a in gains:
            v=(u,a)
            graph.add_node(v,kind=1)
            graph.add_edge((u,None),v,kind=("attach",))
            for j in range(b):
                dest=tuple((x+(i==j))%3 for i,x in enumerate(a))
                graph.add_edge(v,(u,dest),kind=("arc",j))
    for u in range(n):
        for v in range(u):
            for a,c in product(gains,repeat=2):
                m=cells[key(u,v,add(a,c))]
                if m:
                    for x,y in [((u,a),(v,c)),((v,c),(u,a))]:
                        graph.add_edge(x,y,kind=("link",m))
    matcher=DiGraphMatcher(graph,graph,node_match=categorical_node_match("kind",None),
                           edge_match=categorical_edge_match("kind",None))
    actual=set()
    for f in matcher.isomorphisms_iter():
        sigma=tuple(f[u,None][0] for u in range(n))
        p=tuple(f[u,zero][1] for u in range(n))
        assert all(f[u,a]==(sigma[u],add(a,p[u])) for u in range(n) for a in gains)
        actual.add((sigma,p))
    direct=set()
    for sigma in permutations(range(n)):
        for p in product(gains,repeat=n):
            if all(cells[key(sigma[u],sigma[v],add(g,add(p[u],p[v])))]==m
                   for (u,v,g),m in cells.items()):
                direct.add((sigma,p))
    assert actual==direct
    translations=Counter(tuple(sum(a[j] for a in p)%3 for j in range(b)) for _,p in actual)
    assert len(set(translations.values()))==1
    return len(direct),translations


if __name__=="__main__":
    hub=[(0,i,(i%3,)) for i in (1,2,3)]+[(1,2,(0,)),(1,3,(0,)),(2,3,(0,))]
    size,images=check(4,hub,1)
    assert set(images)=={(0,),(1,),(2,)} and images[(0,)]>1
    print("K4 hub",size,images)
    print("uneven vector parallel cells",check(2,[(0,1,(1,2)),(0,1,(1,2)),(0,1,(0,1))],2))
