from itertools import combinations, product
from random import Random
from punctured_witness import BinaryField
from torus_separator_tree import decide
from torus_overlap import _monomial, decide as global_decide


def balanced(ids):
    if len(ids)==1:
        return ids[0]
    mid=len(ids)//2
    return (balanced(ids[:mid]),balanced(ids[mid:]))


def check():
    rng=Random(81271)
    for index in range(48):
        f=BinaryField(7 if index%2 else 19)
        n=rng.randrange(3)
        points=list(product(range(1,f.size),repeat=n))
        def row():
            return tuple(rng.randrange(-3,5) for _ in range(n))
        point=rng.choice(points)
        base=[row() for _ in range(rng.randrange(3))]
        c=[_monomial(f,point,r) for r in base]
        polys=[[(rng.randrange(1,f.size),row()) for _ in range(rng.randrange(1,4))]
               for _ in range(rng.randrange(1,6))]
        def ev(poly,x):
            v=0
            for k,r in poly:
                v ^= f.mul(k,_monomial(f,x,r))
            return v
        truth=any(all(_monomial(f,x,r)==y for r,y in zip(base,c))
                  and all(ev(poly,x) for poly in polys) for x in points)
        ids=list(range(len(polys)))
        rng.shuffle(ids)
        got=decide(f,n,base,c,polys,balanced(ids),max_overlap=300)
        assert got.status == ("SAT" if truth else "UNSAT")

    f=BinaryField(7)
    def edge(n,u,v):
        return [(1,tuple(int(j==i) for j in range(n))) for i in (u,v)]
    triangles=5
    n=2*triangles+1
    polys=[]
    branches=[]
    for i in range(triangles):
        j=len(polys)
        branches.append(((j,j+1),j+2))
        polys.extend(edge(n,u,v) for u,v in combinations((0,2*i+1,2*i+2),2))
    tree=balanced(branches)
    res=decide(f,n,[],[],polys,tree,max_overlap=3)
    assert (res.status,res.max_cut_index,res.peak_states)==("SAT",3,3)
    assert global_decide(f,n,[],[],polys,max_overlap=3).overlap == 3**triangles
    assert decide(f,n,[],[],polys,tree,max_overlap=2).status=="UNKNOWN"
    clique=[edge(4,u,v) for u,v in combinations(range(4),2)]
    assert decide(f,4,[],[],clique,balanced(list(range(6)))).status=="UNSAT"
    print("48 brute-force coset checks, five-triangle cactus, cap and clique controls passed")


if __name__=="__main__":
    check()
