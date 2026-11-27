"""Bounded checks for resilient optional-edge cores. Original witnesses are verified."""
from itertools import combinations
from random import Random
import networkx as nx
from original_dag_quadratic import gauss


def mask(vertices):
    return sum(1<<v for v in vertices)


def even(G,S):
    return all(not (len(set(G[v])&S)%2) for v in S)


def extract(G,k):
    core=set(range(k))
    H=G.subgraph(core).copy()
    F=nx.empty_graph(k)
    routes={}
    for comp in nx.connected_components(G.subgraph(set(G)-core)):
        ends=set().union(*(set(G[v])&core for v in comp))
        assert len(ends)<=2
        if len(ends)!=2:continue
        a,b=sorted(ends)
        sub=G.subgraph(comp|ends).copy()
        if sub.has_edge(a,b):sub.remove_edge(a,b)
        path=nx.shortest_path(sub,a,b)
        F.add_edge(a,b)
        routes[a,b]=path[1:-1]
    return H,F,routes


def raw_sets(G,k,P):
    return {x&((1<<k)-1) for x in range(1<<len(G))
            if x&mask(P)==mask(P) and even(G,{i for i in G if x>>i&1})}


def lift(H,F,S,routes):
    chosen=S.copy()
    for comp in nx.connected_components(F.subgraph(S)):
        tree=nx.bfs_tree(F.subgraph(S),min(comp))
        demand={v:len(set(H[v])&S)%2 for v in comp}
        for v in reversed(list(tree)):
            if not demand[v]:continue
            if v==min(comp):return None
            parent=next(tree.predecessors(v))
            demand[parent]^=1
            chosen.update(routes[tuple(sorted((v,parent)))])
    return chosen


def resilient(F,P):
    comps=list(nx.connected_components(F))
    for C in comps:
        for size in range(min(len(C-P),len(comps)-1)+1):
            for removed in combinations(C-P,size):
                left=C-set(removed)
                if left and not nx.is_connected(F.subgraph(left)):return False
    return True


def count(H,comps,fixed):
    # Only r−1 crossing-parity equations are independent as a list of checks.
    polynomials=[]
    for C in comps[:-1]:
        polynomials.append({(1<<u)|(1<<v) for u,v in H.edges() if (u in C)!=(v in C)})
    total=0
    free=mask(H)^mask(fixed)
    for s in range(1<<len(polynomials)):
        poly=set()
        for i,row in enumerate(polynomials):
            if s>>i&1:poly^=row
        restricted=set()
        for m in poly:restricted.symmetric_difference_update([m&free])
        total+=gauss(restricted,free)
    answer,rem=divmod(total,1<<len(polynomials))
    assert rem==0
    return answer


def check(G,k,P):
    H,F,routes=extract(G,k)
    comps=list(nx.connected_components(F))
    raw=raw_sets(G,k,P)
    loose=set()
    exact=set()
    for b in range(1<<k):
        S={v for v in H if b>>v&1}
        if not P<=S:continue
        wit=lift(H,F,S,routes)
        if wit is not None:
            assert even(G,wit)
            exact.add(b)
        if all(sum(len(set(H[v])&S) for v in C&S)%2==0 for C in comps):loose.add(b)
    assert raw==exact
    assert count(H,comps,P)==len(loose)
    forced=P.copy()
    if loose:
        for i in sorted(set(H)-P):
            size=count(H,comps,forced|{i})
            assert size==sum(b&mask(forced|{i})==mask(forced|{i}) for b in loose)
            if size:forced.add(i)
        assert mask(forced) in loose
        assert k-len(forced)<=2*(len(comps)-1)
        assert all(len(C-forced)<=len(comps)-1 for C in comps)
        if resilient(F,P):
            witness=lift(H,F,forced,routes)
            assert witness is not None and even(G,witness) and P<=witness
    elif resilient(F,P):assert not raw
    return bool(raw),bool(loose),resilient(F,P)


def build(k,base,bridges):
    G=nx.empty_graph(k)
    G.add_edges_from(base)
    for a,b in bridges:
        x=len(G)
        G.add_edges_from([(a,x),(x,b)])
    return G


if __name__=='__main__':
    # Required u,v,w; optional path u-z-v splits when the base edge zw forces z out.
    P={0,1,2}
    assert check(build(4,[(0,1),(2,3)],[(0,3),(1,3)]),4,P)==(False,True,False)
    assert check(build(3,[(0,1)],[]),3,P)==(False,False,True)
    assert check(build(3,[(0,1)],[(0,1),(0,1)]),3,P)==(True,True,True)
    rng=Random(3701)
    summary={}
    for _ in range(120):
        k=rng.randrange(3,7)
        pairs=list(combinations(range(k),2))
        G=build(k,[p for p in pairs if rng.randrange(4)==0],
                [rng.choice(pairs) for _ in range(rng.randrange(5))])
        # An outside piece with a chord, repeated attachments to one endpoint.
        if len(G)>k and rng.randrange(3)==0:
            x=len(G); a=next(iter(G[k]));G.add_edges_from([(x,k),(x,a)])
        if rng.randrange(3)==0:G.add_edge(len(G),0)
        if rng.randrange(4)==0:G.add_node(len(G))
        status=check(G,k,set(rng.sample(range(k),3)))
        summary[status]=summary.get(status,0)+1
    print('120 seeded cases (actual, aggregate, resilient)',summary,'plus 3 structured controls')
