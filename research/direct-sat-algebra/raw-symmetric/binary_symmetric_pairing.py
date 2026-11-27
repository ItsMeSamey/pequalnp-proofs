"""Recover a symmetry pairing from raw ANF and a supplied binary leaf basis.

A trial budget bounds the number of pairing candidates. None is inconclusive.
The linear solution space can be exponentially large; no polynomial search
bound is asserted. Matrix columns and control words use low bits first.
"""
from quadratic_centroid import independent, zero_combinations
from quadratic_target import apply_basis, evaluate_anf


def recover(n,m,constant,linear,pairs,leaves,*,max_trials=None):
    leaves=tuple(leaves)
    if len(leaves)!=m or len(independent(leaves))!=m or any(not 0<x<1<<n for x in leaves):
        return None
    raw=lambda x:evaluate_anf(constant,linear,pairs,x)
    def polar(x,y):
        return raw(x)^raw(y)^raw(x^y)^constant
    if any(polar(x,y) for j,x in enumerate(leaves) for y in leaves[:j]):
        return None
    centers=independent((*leaves,*(1<<i for i in range(n))))[m:]
    if len(centers)<m:
        return None
    matrices=[tuple(polar(x,y) for y in leaves) for x in centers]
    mask=(1<<m)-1
    def image(X,v):
        return apply_basis(tuple((X>>(m*i))&mask for i in range(m)),v)
    def defect(X):
        value=0
        for matrix in matrices:
            cols=[image(X,v) for v in matrix]
            for j in range(m):
                for i in range(j):
                    value=(value<<1)|(((cols[j]>>i)^(cols[i]>>j))&1)
        return value
    space=zero_combinations(tuple(1<<i for i in range(m*m)),defect)
    def candidates():
        yield from space
        for bits in range(1,1<<len(space)):
            if bits.bit_count()>1:
                yield apply_basis(space,bits)
    for trial,X in enumerate(candidates()):
        if max_trials is not None and trial>=max_trials:
            break
        diagonal=tuple(sum(((image(X,v)>>i)&1)<<i for i,v in enumerate(mat)) for mat in matrices)
        if len(independent(diagonal))==m:
            return X,tuple(centers),diagonal
    return None


if __name__=='__main__':
    from random import Random
    from hidden_product_network import encoder
    from quadratic_target import interpolate
    rng=Random(9283)
    def basis(d):
        a=tuple(1<<i for i in range(d))
        for _ in range(8*d):
            i,j=rng.sample(range(d),2)
            b=list(a)
            b[i]^=a[j]
            a=tuple(b)
        return a
    ib,ob=basis(6),basis(3)
    coords=encoder(ib)
    def raw(x):
        z=coords(x)
        t,y=z&7,z>>3
        off=[(t&v).bit_count()%2 for v in (3,7,5)]
        cols=[(t&1)|(off[0]<<1)|(off[1]<<2),off[0]|(t&2)|(off[2]<<2),off[1]|(off[2]<<1)|(t&4)]
        return apply_basis(ob,apply_basis(cols,y)^((z&3)==3)^y)
    anf=interpolate(raw,6)
    assert recover(6,3,*anf,ib[3:]) is not None
    assert recover(6,3,*anf,ib[3:],max_trials=0) is None
    assert recover(6,3,0,[0]*6,{},ib[3:]) is None
    print('hidden pairing, zero budget, and rank-deficient controls passed')
