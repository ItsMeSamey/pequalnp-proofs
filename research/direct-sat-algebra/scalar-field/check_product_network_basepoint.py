from itertools import product
from random import Random
from affine_binomial import power
from product_network_basepoint import solve
from punctured_witness import BinaryField


def compare(f,n,edges,support):
    def satisfy(x):
        return all(f.mul(x[u],power(f,x[v],1<<(t%f.m)))==b for u,v,t,b in edges)
    choices=[range(1,f.size) if i in support else [0] for i in range(n)]
    expected={x for x in product(*choices) if satisfy(x)}
    got=solve(f,n,edges,support)
    if got is None:
        assert not expected
        return
    assert got.values in expected
    charts=[]
    for comp in got.components:
        roots=[h for h in range(1,f.size) if power(f,h,comp.order)==1]
        assert len(roots)==comp.order
        charts.append([(comp.vertices,tuple(f.mul(got.values[v],power(f,h,e%(f.size-1)))
                                            for v,e in zip(comp.vertices,comp.exponents))) for h in roots])
    actual=set()
    for pieces in product(*charts):
        x=[0]*n
        for vs,vals in pieces:
            for j,val in zip(vs,vals):
                x[j]=val
        actual.add(tuple(x))
    assert actual==expected


def check():
    rng=Random(8782)
    checked=0
    for mod in (7,11,19):
        f=BinaryField(mod)
        # Multiple norm-type rows, including incompatible field constants.
        for a in range(1,f.size):
            for b in range(1,f.size):
                compare(f,1,[(0,0,1,a),(0,0,2,b)],{0})
                checked+=1
        for _ in range(80):
            n=rng.randrange(1,4 if mod!=19 else 3)
            x=[rng.randrange(f.size) for _ in range(n)]
            edges=[]
            for j in range(rng.randrange(7)):
                u,v,t=rng.randrange(n),rng.randrange(n),rng.randrange(-f.m,2*f.m)
                b=f.mul(x[u],power(f,x[v],1<<(t%f.m)))
                if rng.randrange(5)==0:
                    b=rng.randrange(f.size)
                edges.append((u,v,t,b))
            support={i for i,z in enumerate(x) if z}
            compare(f,n,edges,support)
            checked+=1
    print(checked,"brute fixed-support comparisons matched full parameterized solution sets")


if __name__=="__main__":
    check()
