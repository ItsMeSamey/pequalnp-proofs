from itertools import combinations,product
from random import Random
import networkx as nx
from planar_ternary_matching import count


def main():
    rng=Random(8101)
    cases=0
    for graph in [g for g in nx.graph_atlas_g() if len(g)<=5]+[
            nx.cubical_graph(),nx.complete_graph(4),nx.cycle_graph(6),nx.path_graph(8)]:
        if not nx.check_planarity(graph)[0]:
            continue
        n=len(graph)
        rows=[(u,v,(rng.randrange(3),rng.randrange(3))) for u,v in graph.edges]
        if rows:
            u,v,g=rows[0]
            rows.append((v,u,g))
        matches=[s for s in combinations(range(len(rows)),n//2) if
                 sorted(x for j in s for x in rows[j][:2])==list(range(n))]
        for t in product(range(3),repeat=2):
            good=[s for s in matches if all(sum(rows[j][2][i] for j in s)%3==v for i,v in enumerate(t))]
            val,w=count(n,rows,t)
            assert val==len(good) and (tuple(sorted(w)) in good if good else w is None)
            cases+=1
    try:
        count(6,[(u,v,()) for u,v in nx.complete_bipartite_graph(3,3).edges],())
    except ValueError:
        pass
    else:
        raise AssertionError("nonplanar graph accepted")
    print(cases,"exact original edge count/witness checks; nonplanar K3,3 rejected")


if __name__=='__main__':
    main()
