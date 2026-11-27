"""Certified finest simultaneous input/output direct factors of a binary quadratic.

Use decompose(n,m,constant,linear,pairs) with quadratic_target's packed ANF.
Requires zero common polar radical and full polar output span. The constant
is translated away; block outputs sum to Q(x)+Q(0). Dimensions and packed
matrix/nullspace arithmetic are polynomial in the explicit input size.
"""
from dataclasses import dataclass
from quadratic_target import apply_basis, evaluate_anf, insert, reduce_vector


def independent(vectors):
    rows = {}
    return tuple(v for v in vectors if insert(v,0,rows))


def zero_combinations(basis, function):
    """Kernel of a linear function on the supplied basis, in ambient encoding."""
    rows = {}
    kernel = []
    for v in basis:
        residue, combination = reduce_vector(function(v),rows)
        if residue:
            rows[residue.bit_length()-1] = residue, v ^ combination
        else:
            kernel.append(v ^ combination)
    return kernel


@dataclass(frozen=True)
class Decomposition:
    # Each idempotent consists of input and output matrices in column encoding.
    idempotents: tuple
    # Each block consists of an ambient input basis and ambient output basis.
    blocks: tuple
    constant: int


def decompose(n,m,constant,linear,pairs,*,polar_only=False):
    """Return finest polar factors when polar_only, else quadratic-compatible factors."""
    if (min(n,m,constant)<0 or len(linear)!=n or any(
            v<0 or v.bit_length()>m for v in (constant,*linear,*pairs.values()))
            or any(not (0<=i<j<n) for i,j in pairs)):
        raise ValueError("invalid squarefree packed ANF")
    if len(independent(pairs.values()))!=m:
        raise ValueError("requires full polar output span")
    unit = tuple(1<<i for i in range(n))
    out_unit = tuple(1<<i for i in range(m))
    def pack(cols,width):
        return sum(col<<(i*width) for i,col in enumerate(cols))
    def unpack(value,k):
        return tuple((value>>(i*k)) & ((1<<k)-1) for i in range(k))
    def decode(v):
        return unpack(v,n),unpack(v>>(n*n),m)
    def encode(s,t):
        return pack(s,n) | (pack(t,m)<<(n*n))
    # polar_rows[j][i] = B(e_i,e_j)
    polar_rows = [tuple(pairs.get(tuple(sorted((i,j))),0) for i in range(n))
                  for j in range(n)]
    if zero_combinations(unit,lambda x: pack([apply_basis(row,x) for row in polar_rows],m)):
        raise ValueError("requires zero common polar radical")

    def centroid_defect(v):
        s,t = decode(v)
        return pack([apply_basis(row,si) ^ apply_basis(t,row[i])
                     for row in polar_rows for i,si in enumerate(s)],m)
    centroid = zero_combinations((1<<i for i in range(n*n+m*m)),centroid_defect)
    def idempotence_defect(v):
        s,t = decode(v)
        return encode([apply_basis(s,x)^x for x in s],[apply_basis(t,y)^y for y in t])
    # Squaring is additive in the commutative centroid, in characteristic two.
    idem = zero_combinations(centroid,idempotence_defect)
    def quadratic_defect(v):
        s,t = decode(v)
        return pack([evaluate_anf(0,linear,pairs,x) ^ apply_basis(t,linear[i])
                     for i,x in enumerate(s)],m)
    # For idempotents E,F, B(Ex,Fx)=0, so this defect is additive here.
    selected = idem if polar_only else zero_combinations(idem,quadratic_defect)
    compatible = tuple(decode(v) for v in selected)
    blocks = [(unit,out_unit)] if n else []
    for s,t in compatible:
        refined = []
        for domain,codomain in blocks:
            for flipped in (False,True):
                inputs = independent(apply_basis(s,x) ^ (x if flipped else 0) for x in domain)
                outputs = independent(apply_basis(t,y) ^ (y if flipped else 0) for y in codomain)
                if inputs or outputs:
                    if not inputs or not outputs:
                        raise ArithmeticError("one-sided block")
                    refined.append((inputs,outputs))
        blocks = refined
    return Decomposition(compatible,tuple(blocks),constant)


def self_test():
    from itertools import combinations
    from random import Random
    from quadratic_target import interpolate
    rng = Random(352)
    def basis(d):
        vecs = []
        while len(vecs)<d:
            vecs = list(independent([*vecs,rng.randrange(1,1<<d)]))
        return vecs
    for crossed in (False,True):
        for _ in range(30):
            a,b = basis(4),basis(2)
            def original(x):
                z = apply_basis(a,x)
                v = ((z&1)*((z>>1)&1)) | ((((z>>2)&1)*((z>>3)&1))<<1)
                if crossed:
                    v ^= (z>>2)&1
                return apply_basis(b,v) ^ 3
            c,lin,pairs = interpolate(original,4)
            result = decompose(4,2,c,lin,pairs)
            assert len(result.blocks)==(1 if crossed else 2)
            for s,t in result.idempotents:
                for x in range(16):
                    sx=apply_basis(s,x)
                    assert apply_basis(s,sx)==sx
                    assert original(sx)^c==apply_basis(t,original(x)^c)
            domains = [x for inp,out in result.blocks for x in inp]
            codomains = [y for inp,out in result.blocks for y in out]
            assert len(independent(domains))==len(domains)==4
            assert len(independent(codomains))==len(codomains)==2
            for inp,out in result.blocks:
                span={apply_basis(out,k) for k in range(1<<len(out))}
                assert all(original(apply_basis(inp,k))^c in span for k in range(1<<len(inp)))
            for (inp,_),(other,_) in combinations(result.blocks,2):
                assert all(original(x)^original(y)^original(x^y)^c==0 for x in inp for y in other)
    for args in [(3,1,0,[0]*3,{(0,1):1}),(2,2,0,[0]*2,{(0,1):1})]:
        try:
            decompose(*args)
        except ValueError:
            continue
        raise AssertionError("degenerate input accepted")


if __name__=="__main__":
    self_test()
    print("60 recodings, crossed terms, idempotents and block certificates passed")
