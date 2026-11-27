from itertools import product
from random import Random
from additive_safe_slope import _safe
from commuting_spread import inverse_columns
from projective_stabilizer_slope import find_columns,transforms
from punctured_witness import BinaryField
from quadratic_target import apply_basis


def check(f,cols):
    d=f.m
    got=find_columns(f,cols,certificate=True)
    exists=False
    for j in range(d):
        basis=transforms(f,cols,j)
        for z in range(1<<len(basis)):
            code=apply_basis(basis,z)
            a,b,c,e=[(code>>(k*d))%(f.size) for k in range(4)]
            if b and f.mul(a,e)!=f.mul(b,c):
                exists=True
                break
        if exists:break
    assert bool(got)==exists
    if got:
        s,j,(a,b,c,e)=got
        assert _safe(f,cols,s) and f.mul(a,e)!=f.mul(b,c)
        for x in range(f.size):
            y=apply_basis(cols,x)
            for _ in range(j):
                x,y=f.mul(x,x),f.mul(y,y)
            assert apply_basis(cols,f.mul(a,x)^f.mul(b,y))==f.mul(c,x)^f.mul(e,y)
    return got


rng=Random(61)
count=0
for mod,cols0 in ((19,(13,3,14,13)),(37,(8,28,0,7,30)),(67,(39,10,27,9,41,6))):
    f=BinaryField(mod)
    assert check(f,cols0)[1]>0
    tested=0
    while tested<8:
        a,b,c,e=[rng.randrange(1,f.size) for _ in range(4)]
        if f.mul(a,e)==f.mul(b,c):continue
        P=[f.mul(a,1<<j)^f.mul(b,y) for j,y in enumerate(cols0)]
        inv=inverse_columns(P)
        if inv is None:continue
        Q=[f.mul(c,1<<j)^f.mul(e,y) for j,y in enumerate(cols0)]
        cols=[apply_basis(Q,v) for v in inv]
        check(f,cols)
        tested+=1;count+=1
f=BinaryField(7)
for cols in product(range(f.size),repeat=f.m):check(f,cols)
print("16 raw maps, three strict semilinear cases and",count,"dense projective recodings replayed")
