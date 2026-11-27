from itertools import product
from random import Random
import networkx as nx
from check_labelled_flip_difference import profile
from primitive_flip_catalogue import build
from labelled_flip_difference import solve


if __name__=='__main__':
    rng=Random(2346)
    tests=0
    for graph in (nx.cycle_graph(12),nx.petersen_graph(),nx.complete_graph(6),nx.complete_bipartite_graph(3,3)):
        n=len(graph)
        es=[(u,v,(rng.randrange(3),rng.randrange(3))) for u,v in graph.edges for _ in range(1+(rng.randrange(5)==0))]
        expected=profile(n,es,2)
        for g in product(range(3),repeat=2):
            status,w,_=solve(n,es,g,primitive=True)
            assert (status=='SAT')==(g in expected) and status!='UNKNOWN'
            if w is not None:
                assert frozenset(w) in expected[g]
            tests+=1
    n=20
    edges=[(i,(i+1)%n,(int(i==0),)) for i in range(n)]
    # Two canonical cycle classes in the cover project to one physical long flip.
    templates,stats=build(n,edges)
    assert stats['lift_cycles']==2 and len(templates)==1 and len(templates[0][1])==10
    assert solve(n,edges,(2,),primitive=True,cycle_cap=1)[0]=='UNKNOWN'
    assert solve(n,edges,(2,),primitive=True,cycle_cap=2)[0]=='UNSAT'
    parallel=[(u,v,(j%3,)) for u,v,_ in edges for j in range(5)]
    templates,stats=build(n,parallel)
    assert len(templates)==81 and stats['physical_cycles']==1 and stats['parallel']==80
    templates,stats=build(3,[(0,1,()),(1,2,()),(2,0,())],cycle_cap=0)
    assert templates is None and stats['lift_cycles']==1
    print(tests,'original multigraph target controls plus long cycle, parallel compression and discarded-projection cap passed')
