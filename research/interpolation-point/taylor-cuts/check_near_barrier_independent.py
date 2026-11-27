"""Independent edge-set enumeration for supplied near-barriers, including parallel IDs."""
from itertools import combinations, product
from random import Random
import networkx as nx

from check_konig_independent import matchings
from labelled_near_barrier import solve


def verify(n, edges, barriers, width):
    attainable = {}
    for ids in matchings(n, edges):
        t=tuple(sum(edges[i][2][j] for i in ids)%3 for j in range(width))
        attainable.setdefault(t,set()).add(frozenset(ids))
    for B in barriers:
        for goal in product(range(3),repeat=width):
            status,ids,stats=solve(n,edges,goal,B)
            assert status == ("SAT" if goal in attainable else "UNSAT")
            if ids is not None:
                assert len(ids)==n//2 and frozenset(ids) in attainable[goal]
            assert stats["port_bound"]==max(0,3*stats["slack"]//2)


def main():
    n=4
    pairs=list(combinations(range(n),2))
    barriers=[[i for i in range(n) if m>>i&1] for m in range(1<<n)]
    for mask in range(1<<len(pairs)):
        edges=[(u,v,((mask+i)%3,)) for i,(u,v) in enumerate(pairs) if mask>>i&1]
        verify(n,edges,barriers,1)
    rng=Random(4845)
    for _ in range(10):
        edges=[(u,v,(rng.randrange(3),rng.randrange(3))) for u,v in combinations(range(6),2)
               for _ in range(rng.randrange(3))]
        verify(6,edges,[rng.sample(range(6),rng.randrange(7))],2)
    r=3
    B=set(range(r+2))
    n=4*r+2
    edges=[(u,v,(int(v in B),)) for u,v in combinations(range(n),2)
           if u in B or (u-r-2)//3==(v-r-2)//3]
    G=nx.Graph();G.add_nodes_from(range(n));G.add_edges_from((u,v) for u,v,_ in edges)
    for u,v in combinations(range(n),2):
        assert len(nx.max_weight_matching(G.subgraph(set(G)-{u,v}),maxcardinality=True))*2==n-2
    verify(n,edges,[B],1)
    for t in range(3):
        s,w,stats=solve(n,edges,(t,),B,slack_cap=2,component_cap=3)
        assert s==("SAT" if t<2 else "UNSAT") and stats["slack"]==2
    assert solve(n,edges,(0,),B,slack_cap=1)[0]=="UNKNOWN"
    assert solve(n,edges,(0,),B,component_cap=2)[0]=="UNKNOWN"
    print("3072 exhaustive support/barrier/target decisions, 90 multigraph goals, 91 bicritical deletions and strict brick controls passed")


if __name__=="__main__":
    main()
