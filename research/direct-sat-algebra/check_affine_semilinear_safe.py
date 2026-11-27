from random import Random
from additive_safe_slope import _safe,_columns
from affine_binomial import power
from affine_semilinear_safe import fixed_locus,find_columns
from punctured_witness import BinaryField
from quadratic_target import apply_basis
rng=Random(7701)
count=hostile=0
for mod in (19,67,283):
    f=BinaryField(mod)
    for trial in range(8):
        b=rng.randrange(1,f.size)
        c=rng.randrange(1,f.size)
        a=[f.mul(c,rng.randrange(2)) for _ in range(f.m)]
        if trial<3:a=[0,c]+[0]*(f.m-2)
        a[0]^=b
        cols=_columns(f,a)
        j,T,psi,offset,basis=fixed_locus(f,cols)
        y,v,k=psi
        fixed={offset^apply_basis(basis,i) for i in range(1<<len(basis))}
        assert fixed=={s for s in range(f.size) if y^f.mul(v,power(f,s,1<<k))==s}
        good={s for s in range(f.size) if _safe(f,cols,s)}
        assert len(fixed&good)%2 and find_columns(f,cols) in good
        if f.m%4==0:
            assert len(basis)<=f.m//4
            sub={s for s in range(f.size) if power(f,s,1<<(f.m//4))==s}
            if not good&sub and a[1] and a[-1]!=power(f,a[1],1<<(f.m-1)):hostile+=1
        count+=1
assert hostile
assert find_columns(BinaryField(11),[0,0,0]) is None
print(count,"raw parity and locus checks;",hostile,"nonselfadjoint cases missed by untranslated fixed field")
