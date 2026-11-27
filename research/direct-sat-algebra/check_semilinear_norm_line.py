from random import Random
from semilinear_norm_line import solve,field_basis
from punctured_witness import BinaryField
from quadratic_image import field_modulus
from affine_binomial import power
from additive_safe_slope import _columns,_safe
from quadratic_target import apply_basis
from hidden_product_network import encoder


def check():
    rng=Random(179)
    cases=0
    for d,e,r in [(6,3,1),(8,4,2),(9,3,1),(12,6,2)]:
        f=BinaryField(field_modulus(d))
        for trial in range(10):
            coeff=[0]*d
            coeff[0]=rng.randrange(f.size)
            coeff[r]=rng.randrange(1,f.size)
            coeff[r+e]=rng.randrange(1,f.size)
            cols=_columns(f,coeff)
            ans=solve(f,cols)
            basis=field_basis(f,e)
            assert (ans is not None)==any(_safe(f,cols,coeff[0]^apply_basis(basis,t)) for t in range(1<<e))
            if ans is not None: assert _safe(f,cols,ans)
            cases+=1
    f=BinaryField(field_modulus(12))
    L=field_basis(f,6)
    eta=next(1<<i for i in range(12) if power(f,1<<i,64)!=1<<i)
    coords=encoder(L+[f.mul(eta,z) for z in L])
    cols=[f.mul(eta,power(f,apply_basis(L,coords(1<<i)>>6),4)) for i in range(12)]
    F=field_basis(f,2)
    assert all(not _safe(f,cols,apply_basis(F,t)) for t in range(4))
    s=solve(f,cols)
    assert _safe(f,cols,s) and power(f,s,64)==s
    print(cases,'subfield-line comparisons; old fixed field entirely singular; new output',s)
if __name__=='__main__':check()
