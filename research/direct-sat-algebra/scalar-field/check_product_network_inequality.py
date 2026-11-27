from itertools import combinations, product
from random import Random
from affine_binomial import power
from product_network_inequality import compile_instance, decide
from punctured_witness import BinaryField
from quadratic_image import Quadratic, evaluate
from quadratic_target import apply_basis, insert, interpolate
from hidden_product_network import recover


def dense_basis(n,rng):
    pivots, cols = {}, []
    while len(cols)<n:
        v = rng.randrange(1,1<<n)
        if insert(v,0,pivots):
            cols.append(v)
    return cols


def term_value(field,term,z):
    c,ex = term
    for x,k in zip(z,ex):
        c=field.mul(c,power(field,x,k))
    return c


def explicit():
    rng=Random(991)
    for modulus in (7,11):
        f=BinaryField(modulus)
        m=f.m
        cols=dense_basis(2*m,rng)
        obs=dense_basis(2*m,rng)
        frames=(cols[:m],cols[m:])
        edges=((0,1,1,obs[:m]),(1,1,0,obs[m:]))
        shift=(1<<(2*m))-2
        offset=5
        form=Quadratic(1,29 % (1<<(2*m)),tuple(combinations(range(2*m),2)))
        for target in (offset,0,3,offset^(1<<(2*m))):
            for want in (0,1):
                truth=False
                inst=compile_instance(f,frames,shift,edges,offset,target,form,want)
                for x,y in product(range(f.size),repeat=2):
                    z=(x,y)
                    raw=shift^apply_basis(cols,x | (y<<m))
                    out=offset^apply_basis(obs,f.mul(x,f.mul(y,y)) | (f.mul(y,y)<<m))
                    truth |= out==target and evaluate([form],raw)==want
                    if inst is not None:
                        bit=0
                        for term in inst.polynomial:
                            bit ^= term_value(f,term,z)
                        assert bit == int(evaluate([form],raw)==want)
                        assert all(term_value(f,a,z)==term_value(f,b,z)
                                   for a,b in inst.equations)==(out==target)
                    else:
                        assert out!=target
                assert decide(f,frames,shift,edges,offset,target,form,want)==truth
    print("16 translated GF4/GF8 target/side-bit controls passed")


def hidden():
    f=BinaryField(7)
    rng=Random(582)
    cols=dense_basis(10,rng)
    outs=dense_basis(10,rng)
    shift,offset=693,847
    def value(x):
        z=apply_basis(cols,x^shift)
        codes=[(z>>(2*i))&3 for i in range(5)]
        labels=[]
        for i,a in enumerate(codes):
            b=codes[(i+1)%5]
            labels.append(f.mul(a,f.mul(b,b) if i%2 else b))
        return offset ^ apply_basis(outs,sum(v<<(2*j) for j,v in enumerate(labels)))
    c,l,p=interpolate(value,10)
    chart=recover(10,10,c,l,p)
    assert chart is not None
    form=Quadratic(1,707,((1,7),(3,8),(0,4)))
    for target in (value(0),value(17),value(955),offset,offset^1024):
        for want in (0,1):
            truth=any(value(x)==target and evaluate([form],x)==want for x in range(1024))
            assert decide(chart.field,chart.frames,chart.shift,chart.edges,chart.output_offset,
                          target,form,want)==truth
    print("10 raw-ANF hidden-cycle side-constraint decisions passed")


if __name__=="__main__":
    explicit()
    hidden()
