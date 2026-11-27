from random import Random
from field_rank_drift import frob_powers
from punctured_witness import BinaryField
from quadratic_centroid import independent
from shifted_frobenius_decode import fits

rng=Random(115)
count=0
for modulus,k in ((11,0),(19,1),(67,1),(283,1),(1033,2)):
    f=BinaryField(modulus)
    for j in range(1,f.m):
        if min(j,f.m-j)+2*k>=f.m:continue
        b,c=rng.randrange(f.size),rng.randrange(1,f.size)
        U=[rng.randrange(f.size) for _ in range(k)]
        V=[rng.randrange(f.size) for _ in range(k)]
        cols=[]
        for i in range(f.m):
            x=1<<i
            y=f.mul(b,x)^f.mul(c,frob_powers(f,x,j)[-1])
            for u,v in zip(U,V):
                if v>>i&1:y^=u
            cols.append(y)
        assert (b,c,j) in list(fits(f,cols,k))
        count+=1
f=BinaryField(19)
for trial in range(8):
    cols=[rng.randrange(f.size) for _ in range(f.m)] if trial else [1<<i for i in range(f.m)]
    brute=set()
    for j in (1,3):
        shifts=[frob_powers(f,1<<i,j)[-1] for i in range(f.m)]
        for b in range(f.size):
            for c in range(f.size):
                rem=[y^f.mul(b,1<<i)^f.mul(c,z) for i,(y,z) in enumerate(zip(cols,shifts))]
                if len(independent(rem))<=1:brute.add((b,c,j))
    assert set(fits(f,cols,1,include_scalar=True))==brute
print(count,"planted exponents and 8 exhaustive candidate-set comparisons passed")
