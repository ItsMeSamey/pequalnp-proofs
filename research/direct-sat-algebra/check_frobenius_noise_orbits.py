from random import Random
from affine_binomial import power
from additive_safe_slope import _safe
from frobenius_noise_orbits import find_columns,find_fit
from punctured_witness import BinaryField

def check():
    rng=Random(5917)
    cases=0
    for modulus,j,k in ((7,1,1),(19,1,1),(19,2,1),(67,2,1),(67,2,2),
                         (67,4,1),(283,3,1),(1033,5,2),(0x40009,6,2),(11,1,0)):
        f=BinaryField(modulus)
        for _ in range(3):
            b=rng.randrange(f.size)
            c=rng.randrange(1,f.size)
            U=[c]+[2*c%f.size or 1 for _ in range(k-1)] if k else []
            V=[(rng.randrange(f.size)>>k<<k)|(1<<i) for i in range(k)]
            cols=[]
            for i in range(f.m):
                y=f.mul(b,1<<i)^f.mul(c,power(f,1<<i,1<<j))
                for v,u in zip(V,U):
                    if (v>>i)&1:y^=u
                cols.append(y)
            if k:assert not _safe(f,cols,b)
            for s in (find_fit(f,cols,k,b,c,j),find_columns(f,cols,k)):
                assert _safe(f,cols,s)
            if k and f.m>2*k:assert find_fit(f,cols,k,b^1,c,j) is None
            cases+=1
    f=BinaryField(67)
    cols=[(1<<i)^int(i==0) for i in range(f.m)]
    assert _safe(f,cols,find_fit(f,cols,1,1,0,1))
    assert _safe(f,cols,find_columns(f,cols,1))
    from deterministic_norm_lift import norm_preimage
    # Check projected GF(64) targets and force a primary order-9 lift.
    f=BinaryField(0x40009)
    scale=(f.size-1)//63
    for i in range(1,22):
        n=power(f,i,scale)
        assert power(f,norm_preimage(f,6,n),scale)==n
    n=next(v for v in (power(f,i,scale) for i in range(1,f.size)) if power(f,v,21)!=1)
    assert power(f,norm_preimage(f,6,n),scale)==n
    print(cases,"raw/supplied orbit fixtures, scalar branch, repeated Sylow targets passed")
if __name__=="__main__":check()
