from itertools import combinations,product
from random import Random
from hidden_product_network import recover as old
from punctured_witness import BinaryField
from product_network_witness import witness
from quadratic_image import Quadratic,evaluate
from quadratic_target import apply_basis,insert,interpolate
from untwisted_graph_refinement import recover


def check():
    rng=Random(719)
    def dense(n):
        cols,pivots=[],{}
        while len(cols)<n:
            v=rng.randrange(1,1<<n)
            if insert(v,0,pivots): cols.append(v)
        return cols
    graphs=[(2,[(0,1)]),(3,list(combinations(range(3),2))),
            (4,[(0,1),(0,2),(0,3)]),(4,[(0,2),(0,3),(1,2),(1,3)]),
            (4,[(0,1),(1,2),(2,3)])]
    for d,edges in graphs:
        f=BinaryField(7)
        n,o=2*d,2*len(edges)
        inp,out=dense(n),dense(o)
        shift,offset=rng.randrange(1<<n),rng.randrange(1<<o)
        scales=[rng.randrange(1,4) for _ in edges]
        def original(x):
            a=apply_basis(inp,x^shift)
            p=sum(f.mul(c,f.mul(a>>(2*i)&3,a>>(2*j)&3))<<(2*k)
                  for k,((i,j),c) in enumerate(zip(edges,scales)))
            return offset^apply_basis(out,p)
        c,l,p=interpolate(original,n)
        chart=recover(n,o,c,l,p)
        assert chart is not None,(d,edges)
        assert old(n,o,c,l,p) is None
        for a in product(range(4),repeat=d):
            assert chart.output(a)==original(chart.raw_input(a))
        target=original(3)
        form=Quadratic(1,3,((0,n-1),))
        for want in (0,1):
            w=witness(chart,target,form,want)
            truth=any(original(x)==target and evaluate([form],x)==want for x in range(1<<n))
            assert (w is not None)==truth
            if w is not None: assert original(w)==target and evaluate([form],w)==want
    print("Five dense GF4 graphs passed all raw assignments and 10 side-bit decisions")


if __name__=="__main__":
    check()
