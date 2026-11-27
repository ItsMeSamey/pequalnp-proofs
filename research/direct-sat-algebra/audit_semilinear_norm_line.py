"""Compare exact binary kernel counts against the B^m spectrum, without _safe."""
from random import Random
from math import gcd
from punctured_witness import BinaryField
from quadratic_image import field_modulus
from affine_binomial import power
from quadratic_target import apply_basis
from semilinear_norm_line import solve,field_basis
from hidden_product_network import encoder


def check(f,e,j,b,cols):
    g=gcd(j,e)
    m=e//g
    n=f.m//e
    L=[apply_basis(field_basis(f,e),i) for i in range(1<<e)]
    H=set(x for x in L if power(f,x,1<<g)==x)
    exponent=((1<<e)-1)//((1<<g)-1)
    B=[y^f.mul(b,1<<i) for i,y in enumerate(cols)]
    Bm=[1<<i for i in range(f.m)]
    for _ in range(m):
        Bm=[apply_basis(B,x) for x in Bm]
    kernel={}
    eig={}
    for x in range(1,f.size):
        inv=f.inverse(x)
        s=f.mul(apply_basis(B,x),inv)
        v=f.mul(apply_basis(Bm,x),inv)
        kernel[s]=1+kernel.get(s,0)
        eig[v]=1+eig.get(v,0)
    sizes={}
    for y in L:
        norm=power(f,y,exponent)
        assert norm in H
        count=kernel.get(y,0)
        assert (count>0)==(norm in eig)
        assert sizes.setdefault(norm,count)==count
    assert len(H&set(eig))<=n
    ans=solve(f,cols)
    safe=[b^y for y in L if y not in kernel]
    assert (ans is None)==(not safe) and (ans is None or ans in safe)
    if len(H)>n:
        assert safe
    return sizes


if __name__=='__main__':
    rng=Random(17985)
    cases=0
    for d,e,j in ((4,2,1),(6,3,2),(8,4,3),(9,3,2),(10,5,3),(12,6,4)):
        f=BinaryField(field_modulus(d))
        for _ in range(5):
            b=rng.randrange(f.size)
            a,c=rng.randrange(1,f.size),rng.randrange(1,f.size)
            cols=[f.mul(b,1<<i)^f.mul(a,power(f,1<<i,1<<j))^f.mul(c,power(f,1<<i,1<<(e+j))) for i in range(d)]
            check(f,e,j,b,cols)
            cases+=1
    f=BinaryField(field_modulus(12))
    L=field_basis(f,6)
    eta=next(1<<i for i in range(12) if power(f,1<<i,64)!=1<<i)
    decode=encoder([*L,*[f.mul(eta,v) for v in L]])
    B=[f.mul(eta,power(f,apply_basis(L,decode(1<<i)>>6),4)) for i in range(12)]
    sizes=check(f,6,2,0,B)
    assert sizes[0]==63 and sizes[1]==3 and sorted(sizes.values())==[0,0,3,63]
    print(cases,'complete line/spectrum tables; GF4096 nonzero-kernel counts by norm',sizes)
