"""Witnesses for diagonal-normalized symmetric field pencils.

entries[(i,j)] = (constant, coefficient tuple), i<j, defines the off-diagonal
affine form. Diagonal entries are t_i. Binary drift columns map packed leaf
bits to packed output bits. All input/output chunks use low-first field bits.
"""
from itertools import product
from hidden_product_network import encoder
from quadratic_centroid import independent, zero_combinations
from quadratic_target import apply_basis


def columns(f,r,entries,t):
    matrix=[[0]*r for _ in range(r)]
    for i in range(r):
        matrix[i][i]=t[i]
    for (i,j),(base,coeff) in entries.items():
        value=base
        for a,x in zip(coeff,t):
            value^=f.mul(a,x)
        matrix[i][j]=matrix[j][i]=value
    return tuple(sum(f.mul(matrix[i][j],1<<k)<<(i*f.m) for i in range(r))
                 for j in range(r) for k in range(f.m))


def subfield_basis(f,r,drift):
    """Largest certifiable subfield having enough elements for line search."""
    n=r*f.m
    units=tuple(1<<j for j in range(f.m))
    def scale(a,x):
        return sum(f.mul(a,(x>>(j*f.m))&(f.size-1))<<(j*f.m) for j in range(r))
    for e in range(f.m,0,-1):
        if f.m%e or (1<<e)<=r*(f.m//e):
            continue
        def fixed(x):
            y=x
            for _ in range(e):
                y=f.mul(y,y)
            return y^x
        basis=zero_combinations(units,fixed)
        if all(apply_basis(drift,scale(a,1<<k))==scale(a,drift[k]) for a in basis for k in range(n)):
            return basis
    return ()


def witness(f,r,entries,target,offset,*,binary_drift=None):
    """Return field controls and packed leaves. offset(t) is any center-only map.

    Use three-trial Schur extension on endpoint-dependent off-diagonals over
    fields of size >2 with symmetric field-linear drift, or degree-bounded trials
    for arbitrary affine entries when field.size>r. Otherwise enumerate
    centers until a verified invertible leaf matrix is found.
    """
    n=f.m*r
    if r<0 or not 0<=target<1<<n:
        raise ValueError("invalid dimension or target")
    for (i,j),(c,coeff) in entries.items():
        if not 0<=i<j<r or len(coeff)!=r or any(not 0<=a<f.size for a in (c,*coeff)):
            raise ValueError("invalid symmetric affine entry")
    drift=tuple(binary_drift) if binary_drift is not None else (0,)*n
    if len(drift)!=n or any(not 0<=x<1<<n for x in drift):
        raise ValueError("invalid binary drift")
    def matrix(t):
        return tuple(a^b for a,b in zip(columns(f,r,entries,t),drift))
    local=all(all(not a or k in (i,j) for k,a in enumerate(coeff))
              for (i,j),(_,coeff) in entries.items())
    mask=f.size-1
    constants=[[((drift[j*f.m]>>(i*f.m))&mask) for j in range(r)] for i in range(r)]
    symmetric=all(constants[i][j]==constants[j][i] and all(
        ((drift[j*f.m+k]>>(i*f.m))&mask)==f.mul(constants[i][j],1<<k)
        for k in range(f.m)) for i in range(r) for j in range(r))
    if symmetric and ((f.size>2 and local) or f.size>r):
        t=[0]*r
        for i in range(r):
            d=f.m*(i+1)
            for trial in range(min(3,f.size) if local else i+2):
                t[i]=trial
                cols=matrix(t)[:d]
                if len(independent(x&((1<<d)-1) for x in cols))==d:
                    break
            else:
                raise ArithmeticError("Schur extension failed")
        t=tuple(t)
    elif f.size>r and (basis:=subfield_basis(f,r,drift)):
        # Obtain an invertible homogeneous direction, then test its scalar line.
        homogeneous={edge:(0,coeff) for edge,(_,coeff) in entries.items()}
        direction,_=witness(f,r,homogeneous,0,lambda t:0)
        degree=r*(f.m//len(basis))
        for code in range(degree+1):
            scalar=apply_basis(basis,code)
            t=tuple(f.mul(scalar,x) for x in direction)
            if len(independent(matrix(t)))==n:
                break
        else:
            raise ArithmeticError("subfield determinant line vanished")
    else:
        t=next(t for t in product(range(f.size),repeat=r) if len(independent(matrix(t)))==n)
    cols=matrix(t)
    base=offset(t)
    y=encoder(cols)(target^base)
    if apply_basis(cols,y)^base!=target:
        raise ArithmeticError("witness mismatch")
    return t,y


if __name__=='__main__':
    from punctured_chart import TableField
    from punctured_witness import BinaryField
    from random import Random
    rng=Random(2479)
    # Independent injectivity reference by directly enumerating all leaf words.
    def invertible(cols):
        return all(apply_basis(cols,y) for y in range(1,1<<len(cols)))
    f=TableField(((1,),))
    counts=0
    for c,a,b in product(range(2),repeat=3):
        entries={(0,1):(c,(a,b))}
        for drift in product(range(4),repeat=2):
            good=[t for t in product(range(2),repeat=2)
                  if invertible(tuple(x^z for x,z in zip(columns(f,2,entries,t),drift)))]
            assert len(good)%2==1
            counts+=1
    entries={(0,1):(0,(0,1))}
    assert [t for t in product(range(2),repeat=2) if invertible(columns(f,2,entries,t))]==[(0,1)]
    f=BinaryField(7)
    for c,a,b in product(range(4),repeat=3):
        entries={(0,1):(c,(a,b))}
        assert sum(invertible(columns(f,2,entries,t)) for t in product(range(4),repeat=2))%2==1
        for target in range(16):
            offset=lambda t:f.mul(t[0],t[1])
            t,y=witness(f,2,entries,target,offset)
            assert apply_basis(columns(f,2,entries,t),y)^offset(t)==target
    for _ in range(12):
        entries={(i,j):(rng.randrange(4),tuple(rng.randrange(4) for _ in range(3)))
                 for i,j in ((0,1),(0,2),(1,2))}
        # Nonlocal constructive branch with a nonzero symmetric field drift.
        shift=tuple((f.mul(2,1<<k)<<(2*j)) for j in range(3) for k in range(2))
        t,w=witness(f,3,entries,37,lambda t:6,binary_drift=shift)
        assert apply_basis(tuple(c^a for c,a in zip(columns(f,3,entries,t),shift)),w)^6==37
        nonsymmetric=tuple((1<<k) if j==1 else 0 for j in range(3) for k in range(2))
        t,w=witness(f,3,entries,18,lambda t:0,binary_drift=nonsymmetric)
        assert apply_basis(tuple(c^a for c,a in zip(columns(f,3,entries,t),nonsymmetric)),w)==18
        drift=tuple(rng.randrange(64) for _ in range(6))
        def cols(t):
            return tuple(x^z for x,z in zip(columns(f,3,entries,t),drift))
        assert sum(invertible(cols(t)) for t in product(range(4),repeat=3))%2==1
        t,y=witness(f,3,entries,54,lambda t:9,binary_drift=drift)
        assert apply_basis(cols(t),y)^9==54
    f=BinaryField(19)
    drift=tuple(f.mul(f.mul(x,x),f.mul(x,x)) for x in (1,2,4,8))
    assert len(subfield_basis(f,1,drift))==2
    for target in range(16):
        t,y=witness(f,1,{},target,lambda t:3,binary_drift=drift)
        assert f.mul(t[0],y)^apply_basis(drift,y)^3==target
    print(counts,'exhaustive GF2 pencil/drift pairs; 64 GF4 pencils, 1024 witnesses, 12 dense GF4 controls passed')
