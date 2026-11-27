from itertools import combinations,product
from random import Random
from hidden_uniform_refinement import recover,decide
from punctured_witness import BinaryField
from quadratic_target import apply_basis,insert


def coefficients(fn,n,d):
    table={sum(1<<i for i in ids):fn(sum(1<<i for i in ids))
           for k in range(d+1) for ids in combinations(range(n),k)}
    for j in range(n):
        for v in table:
            if v>>j & 1:
                table[v] ^= table[v^(1<<j)]
    return {v:c for v,c in table.items() if c}


def check():
    f=BinaryField(7)
    rng=Random(180)
    def dense(n):
        a,p=[],{}
        while len(a)<n:
            v=rng.randrange(1,1<<n)
            if insert(v,0,p): a.append(v)
        return a
    for nv,edges in ((3,[(0,1,2)]),(4,[(0,1,2),(0,1,3)]),
                     (4,list(combinations(range(4),3)))):
        n,o=2*nv,2*len(edges)
        ib,ob=dense(n),dense(o)
        shift,offset=rng.randrange(1<<n),rng.randrange(1<<o)
        def raw(x):
            z=apply_basis(ib,x^shift)
            y=0
            for j,e in enumerate(edges):
                a=1
                for i in e: a=f.mul(a,z>>(2*i)&3)
                y |= a<<(2*j)
            return offset^apply_basis(ob,y)
        anf=coefficients(raw,n,3)
        chart=recover(n,o,anf,3)
        assert chart is not None,(nv,edges)
        for point in product(range(4),repeat=nv):
            assert chart.output(point)==raw(chart.raw_input(point))
        pred={0:1,1:1,3:1,7:1,28:1}
        for target in (raw(5),offset,offset^(1<<o)):
            for bit in (0,1):
                truth=any(raw(x)==target and
                          sum((x&a)==a for a in pred)%2==bit for x in range(1<<n))
                assert decide(chart,target,pred,bit)==truth
    def bad(x):
        a,b,c=x&3,(x>>2)&3,(x>>4)&3
        def cube(v):
            return f.mul(v,f.mul(v,v))
        return f.mul(a,f.mul(b,c))^cube(a)^cube(b)^f.mul(2,cube(c))
    assert recover(6,2,coefficients(bad,6,3),3) is None
    print("Three dense cubic hypergraphs verified pointwise, 18 bounded-degree side decisions and smooth repeated-variable cubic rejection passed")


if __name__=="__main__":
    check()
