from itertools import combinations, product
from ternary_chirality_graph import compile_graph
from ternary_frame import color,kernel_obstruction


def run():
    for rank in (1,2):
        vectors=list(product(range(3),repeat=rank))
        for cols in combinations(vectors,4 if rank==2 else 2):
            cert=kernel_obstruction(dict(enumerate(cols)))
            if cert is not None:
                assert not any(all(sum(s*a[j] for s,a in zip(signs,cols))%3==0
                                   for j in range(rank)) for signs in product((1,2),repeat=len(cols)))
    cert=kernel_obstruction(dict(enumerate([(2,2),(2,1),(1,0),(0,1)])))
    assert cert["kind"]=="pencil" and len(set(cert["indices"]))==4
    g=compile_graph(4,[(-1,-1,1,0),(-1,1,0,1)])
    assert color(g.order,g.edges,cap=0,use_prism=True)[0]=="UNSAT"
    edges=[]
    for i in range(5):
        edges.extend(combinations(range(3*i,3*i+3),2))
        edges.extend((3*i+j,3*((i+1)%5)+(j if i!=4 else (-j)%3)) for j in range(3))
    s,_,stats=color(15,edges,cap=0,use_prism=True)
    assert s=="UNSAT" and stats["certificate"]["kind"]=="inconsistent signed cycle"
    print("pencil, twisted ring and compiled graph pre-cap certificates passed")


if __name__=="__main__":
    run()
