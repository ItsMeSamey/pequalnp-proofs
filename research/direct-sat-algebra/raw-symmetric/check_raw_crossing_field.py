from itertools import combinations
from random import Random
from hidden_product_network import encoder
from punctured_witness import BinaryField
from quadratic_target import apply_basis,insert,interpolate
from raw_crossing_field import recover
from raw_symmetric_leaves import recover as discover_leaves
from extension_field_target import centroid


def check():
    rng=Random(556)
    def dense(n):
        pivots,cols={},[]
        while len(cols)<n:
            x=rng.randrange(1,1<<n)
            if insert(x,0,pivots): cols.append(x)
        return cols
    f=BinaryField(7)
    passed=0
    for a,b in ((1,2),(3,1),(2,2),(1,1),(3,3),(2,3),(1,3),(2,1)):
        dom,out=dense(8),dense(4)
        decode=encoder(dom)
        coeff=[rng.randrange(16) for _ in combinations(range(4),2)]
        def raw(x):
            w=decode(x)
            t,u,y,z=[(w>>(2*i))&3 for i in range(4)]
            off=f.mul(a,t)^f.mul(b,u)
            v=f.mul(t,y)^f.mul(off,z)
            w2=f.mul(off,y)^f.mul(u,z)
            # Field-linear leaf drift and arbitrary quadratic center-only g.
            g=7^y
            for c,(i,j) in zip(coeff,combinations(range(4),2)):
                if w>>i&w>>j&1: g ^= c
            return apply_basis(out,v^(w2<<2)^g)
        args=interpolate(raw,8)
        chart=recover(8,4,*args,degree=2,max_trials=256)
        if chart is None: continue
        assert chart.r==2 and chart.field.size==4
        assert all(raw(chart.witness(t))==t for t in range(16))
        passed+=1
    assert passed, "failed to recover any two-dimensional field pencil"
    print(passed,"of 8 raw-only cross-coupled dense GF4 two-by-two pencils recovered, all 16 targets verified for each")


if __name__=="__main__":
    check()


def noncommuting():
    f=BinaryField(7)
    rng=Random(912)
    def dense(n):
        pivots,cols={},[]
        while len(cols)<n:
            v=rng.randrange(1,1<<n)
            if insert(v,0,pivots): cols.append(v)
        return cols
    dom,out=dense(12),dense(6)
    decode=encoder(dom)
    terms=[(i,j,rng.randrange(64)) for i,j in combinations(range(6),2)]
    def raw(x):
        w=decode(x)
        t=[w>>(2*j)&3 for j in range(3)]
        y=[w>>(6+2*j)&3 for j in range(3)]
        v=0
        for i in range(3):
            j,k=(i+1)%3,(i+2)%3
            value=f.mul(2 if i==0 else 1,f.mul(t[i],y[i]))^f.mul(2,f.mul(t[j],y[k])^f.mul(t[k],y[j]))
            v ^= value<<(2*i)
        for i,j,c in terms:
            if w>>i&w>>j&1: v^=c
        return apply_basis(out,v^7)
    anf=interpolate(raw,12)
    leaf=discover_leaves(12,6,*anf,max_pairing_trials=256)
    assert leaf and leaf.method=="central nilpotent" and all(decode(v)&63==0 for v in leaf.leaves)
    _,centers,_=leaf.pairing
    cross={(i,6+j):raw(u)^raw(v)^raw(u^v)^raw(0)
           for i,u in enumerate(centers) for j,v in enumerate(leaf.leaves)}
    assert len(centroid(12,6,cross))==2
    chart=recover(12,6,*anf,degree=2,max_trials=256)
    assert chart and chart.r==3
    assert all(raw(chart.witness(t))==t for t in range(64))
    print("Three-by-three fully overlapping GF4 pencil: central-nilpotent leaf, 64 verified targets")


if __name__=="__main__":
    noncommuting()
