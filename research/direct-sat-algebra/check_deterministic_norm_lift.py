from affine_binomial import power
from deterministic_norm_lift import norm_preimage
from punctured_witness import BinaryField
from quadratic_centroid import zero_combinations
from quadratic_target import apply_basis

count=0
for mod in (7,11,19,37,67,283):
    f=BinaryField(mod)
    for g in range(1,f.m+1):
        if f.m%g:continue
        e=(f.size-1)//((1<<g)-1)
        fibers={}
        for y in range(1,f.size):fibers.setdefault(power(f,y,e),set()).add(y)
        for n,values in fibers.items():
            assert norm_preimage(f,g,n) in values
            count+=1
for d,g in ((18,6),(20,4)):
    for p in range((1<<d)+1,(1<<d)+4096,2):
        try:f=BinaryField(p)
        except ValueError:continue
        break
    basis=zero_combinations([1<<i for i in range(d)],lambda x:x^power(f,x,1<<g))
    for i in range(1,1<<g):
        n=apply_basis(basis,i)
        assert power(f,norm_preimage(f,g,n),(f.size-1)//((1<<g)-1))==n
        count+=1
print(count,"norm targets verified, including primary order 9 and prime 5")
