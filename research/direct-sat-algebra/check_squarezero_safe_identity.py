"""Independent verification using sparse dictionaries and Leibniz determinants."""
from itertools import permutations,product
from random import Random
from additive_slope_prefix import dickson
from affine_binomial import power
from punctured_witness import BinaryField
from quadratic_target import apply_basis


def add(a,b):
    r=a.copy()
    for k,c in b.items():
        r[k]=r.get(k,0)^c
        if not r[k]:
            del r[k]
    return r


def times(f,a,b):
    out={}
    for i,x in a.items():
        for j,y in b.items():
            if not i&j:
                out=add(out,{i|j:f.mul(x,y)})
    return out


def ring_product(f,items):
    out={0:1}
    for q in items:
        out=times(f,out,q)
    return out


def verify(f,coeff,rows):
    d=f.m
    h=len(rows)
    constant={0:1}
    B=[{} for _ in range(d)]
    for j,(alpha,c) in enumerate(rows):
        if c:
            constant=times(f,constant,{0:1,1<<j:c})
        for i in range(d):
            carry={1<<j:alpha} if alpha else {}
            pos=i
            while carry:
                old=B[pos]
                B[pos]=add(old,carry)
                carry=times(f,old,carry)
                pos=(pos+1)%d
            alpha=f.mul(alpha,alpha)
    D=dickson(f,coeff)
    mat=[[add({0:1} if i==j else {},times(f,B[i],{0:D[i][j]})) for j in range(d)] for i in range(d)]
    det={}
    for p in permutations(range(d)):
        det=add(det,ring_product(f,[mat[i][p[i]] for i in range(d)]))
    actual=times(f,constant,add(det,ring_product(f,B)))
    def evalA(x):
        z=0
        for coeff_i in coeff:
            z^=f.mul(coeff_i,x)
            x=f.mul(x,x)
        return z
    bad={f.mul(evalA(x),f.inverse(x)) for x in range(1,f.size)}
    wanted={}
    for s in range(f.size):
        terms=[{0:1,1<<j:c^f.trace(f.mul(alpha,s))} for j,(alpha,c) in enumerate(rows)]
        inp=ring_product(f,terms)
        # Check the carry stage as a full function, on all slopes.
        after=times(f,constant,ring_product(f,[add({0:1},times(f,b,{0:power(f,s,1<<i)})) for i,b in enumerate(B)]))
        assert after==inp
        if s not in bad:
            wanted=add(wanted,inp)
    assert actual==wanted


if __name__=='__main__':
    rng=Random(479)
    cases=0
    for modulus in (7,11,19):
        f=BinaryField(modulus)
        maps=list(product(range(f.size),repeat=f.m)) if f.m==2 else []
        maps.extend([[0]*f.m,[1],[0,1],[1,1],*(tuple(rng.randrange(f.size) for _ in range(f.m)) for _ in range(10))])
        for a in maps:
            for h in (0,1,f.m//2,f.m,f.m+1):
                rows=[(rng.randrange(f.size),rng.randrange(f.size)) for _ in range(h)]
                verify(f,a,rows)
                cases+=1
    print(cases,'full ring identities and carry-stage function checks, including h>=d')
