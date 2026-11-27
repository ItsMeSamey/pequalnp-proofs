from itertools import combinations
from random import Random
from hidden_product_network import encoder
from punctured_witness import BinaryField
from quadratic_target import apply_basis,insert,interpolate
from raw_symmetric_leaves import recover


def check():
    rng=Random(1176)
    def dense(n):
        basis,pivots=[],{}
        while len(basis)<n:
            v=rng.randrange(1,1<<n)
            if insert(v,0,pivots): basis.append(v)
        return basis
    passed=[]
    for modulus in (11,19):
        f=BinaryField(modulus)
        m=f.m
        for trial in range(5):
            ib,ob=dense(2*m),dense(m)
            decode=encoder(ib)
            drift=[rng.randrange(f.size) for _ in range(m)]
            terms=[(1<<i|1<<j,rng.randrange(f.size)) for i,j in combinations(range(m),2)]
            shift=rng.randrange(1<<(2*m))
            offset=rng.randrange(f.size)
            def raw(x,with_g=True):
                z=decode(x^shift)
                t,y=z&(f.size-1),z>>m
                gy=0
                if with_g:
                    for p,c in terms:
                        if t&p==p: gy^=c
                return offset^apply_basis(ob,f.mul(t,y)^gy^apply_basis(drift,y))
            anf=interpolate(raw,2*m)
            result=recover(2*m,m,*anf,max_pairing_trials=300)
            if result:
                assert all(decode(v)%(1<<m)==0 for v in result.leaves)
                assert len(result.leaves)==m
                passed.append(m)
            assert recover(2*m,m,*interpolate(lambda x:raw(x,False),2*m)) is None
    assert passed.count(3)>=2 and passed.count(4)>=2
    assert recover(6,3,0,[0]*6,{}) is None
    print("Recovered planted leaves in",len(passed),"of 10 dense GF8/GF16 overlapping pencils; all 10 commuting controls inconclusive")


if __name__=="__main__":
    check()
