from random import Random
from mixed_product_network import solve, scalar_form
from punctured_witness import BinaryField
from quadratic_image import Quadratic, evaluate, parity
from quadratic_target import apply_basis, insert, interpolate


def check():
    f=BinaryField(7)
    rng=Random(871)
    def dense(n):
        pivots,cols={},[]
        while len(cols)<n:
            v=rng.randrange(1,1<<n)
            if insert(v,0,pivots):
                cols.append(v)
        return cols
    cols,outs=dense(15),dense(15)
    shift,offset=17402,23419
    def value(x):
        z=apply_basis(cols,x^shift)
        pairs=[]
        for i in range(5):
            u,v=(z>>(2*i))&3,(z>>(2*((i+1)%5)))&3
            pairs.append(f.mul(u,f.mul(v,v) if i%2 else v))
        y=sum(v<<(2*i) for i,v in enumerate(pairs))
        for j in range(5):
            y |= ((z>>(10+j))&(z>>(10+(j+1)%5))&1)<<(10+j)
        return offset^apply_basis(outs,y)
    c,l,p=interpolate(value,15)
    def run(t,form,want=1):
        res=solve(15,15,c,l,p,t,form,want)
        if res.status=="SAT":
            assert value(res.witness)==t and evaluate([form],res.witness)==want
        return res
    base=run(offset,Quadratic(1))
    assert base.changed_blocks==0 and sorted(base.degrees)==[1,2]
    at=base.witness
    # Each entire coordinate ranges freely on some zero-target assignments.
    def fbit(x,k):
        return (apply_basis(cols,x^at)>>k)&1
    left=scalar_form(lambda x:fbit(x,0),15)
    cross=scalar_form(lambda x:fbit(x,0)*fbit(x,10),15)
    assert run(offset,left).changed_blocks==1
    assert run(offset,cross).changed_blocks==2
    assert run(offset,Quadratic()).status=="UNSAT"
    goal=value(7713)
    form=Quadratic(0,18819,((0,7),(1,13),(3,9)))
    truth={evaluate([form],x) for x in range(1<<15) if value(x)==goal}
    for bit in (0,1):
        assert (run(goal,form,bit).status=="SAT")== (bit in truth)
    assert solve(3,1,0,[0]*3,{(0,1):1},0,Quadratic()).status=="UNKNOWN"
    print("Dense F2/F4 cycles: zero-, one-, two-block witnesses, absent side bit, two exhaustive decisions and unknown control passed")


if __name__=="__main__":
    check()
