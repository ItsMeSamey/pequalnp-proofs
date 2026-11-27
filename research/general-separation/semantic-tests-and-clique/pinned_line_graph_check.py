"""Finite tree-certificate enumerator for mandatory vertices of line graphs."""
from itertools import combinations,product
from random import Random
import networkx as nx


def endpoints(edges):
    return {x for e in edges for x in e}


def valid_line(edges,selection):
    # Direct induced degrees of the selected vertices in L(B).
    return all(sum(len(set(e)&set(f))==1 for f in selection if f!=e)%2==0 for e in selection)


def certify(edges,forced,surplus=1):
    F=set(forced)
    if not F:return set()
    terminals=endpoints(F)
    optional=[e for e in edges if e not in F]
    degF={i:sum(i in e for e in F) for i in terminals}
    for mask in range(1<<len(optional)):
        chosen=[e for i,e in enumerate(optional) if mask>>i&1]
        V=endpoints(chosen)|terminals
        graph={v:[] for v in V}
        for a,b in chosen:graph[a].append(b);graph[b].append(a)
        todo=V.copy()
        comps=[]
        while todo:
            root=min(todo)
            prev={root:None}
            order=[root]
            for v in order:
                for w in graph[v]:
                    if w not in prev:prev[w]=v;order.append(w)
            todo.difference_update(order)
            if (len(order)-1)*2!=sum(len(graph[v]) for v in order) or not terminals.intersection(order):
                break
            if sum(v not in terminals and len(graph[v])<=1 for v in order)>surplus:break
            comps.append((prev,order))
        else:
            label={v:i for i,(_,C) in enumerate(comps) for v in C}
            for color in product((0,1),repeat=len(comps)):
                if any(color[label[a]]!=color[label[b]] for a,b in F):continue
                if any((sum(degF.get(v,0) for v in C)-c*len(C))%2 for c,(_,C) in zip(color,comps)):continue
                D=F.copy()
                for c,(prev,C) in zip(color,comps):
                    demand={v:(degF.get(v,0)^c)&1 for v in C}
                    for v in reversed(C[1:]):
                        if demand[v]:
                            u=prev[v]
                            demand[u]^=1
                            D.add(tuple(sorted((u,v))))
                    assert not demand[C[0]]
                assert F<=D and valid_line(edges,D)
                return D
    return None


def oracle(edges):
    hits=set()
    for mask in range(1<<len(edges)):
        selected=[e for i,e in enumerate(edges) if mask>>i&1]
        if valid_line(edges,selected):
            for k in range(min(3,len(selected))+1):hits.update(combinations(selected,k))
    return hits


def main():
    rng=Random(6783);cases=0;example=None
    for G in nx.graph_atlas_g():
        n=len(G)
        if n>5:continue
        E=sorted(tuple(sorted(e)) for e in G.edges())
        answers=oracle(E)
        for k in range(min(3,len(E))+1):
            for F in combinations(E,k):
                success=certify(E,F) is not None
                assert success==(F in answers)
                cases+=1
                if example is None and success and certify(E,F,0) is None:example=(E,F)
    assert example is not None
    for _ in range(45):
        n=rng.randrange(6,10)
        poss=list(combinations(range(n),2))
        E=sorted(rng.sample(poss,rng.randrange(3,11)))
        answers=oracle(E)
        F=tuple(sorted(rng.sample(E,3)))
        assert (certify(E,F) is not None)==(F in answers)
        cases+=1
    from high_connectivity_anchor_check import host
    for t in range(1,4):
        for yes in (False,True):
            g,_,_,_=host(t,yes)
            witness=next((v,a,b,c) for v in g for a,b,c in combinations(g[v],3)
                         if not any(g.has_edge(i,j) for i,j in combinations((a,b,c),2)))
            assert g.subgraph(witness).number_of_edges()==3
    print(cases,'instances; necessary surplus leaf example',example,'six anchor claws found')


if __name__=='__main__':main()
