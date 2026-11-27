"""Extract a Boolean rank-one locus when minors reduce products to linear functions.

rank_one_matrices(r,basis) takes symmetric packed r-by-r binary matrices. None
means that this linear-function algebra test did not certify the locus. A
tuple lists all nonzero rank-one matrices in the span; its vectors are checked
directly. prepare(n,r,c,linear,pairs) tries the supplied/raw symmetric pairing
and builds a polynomial-size witness chart when r independent range vectors
can be selected. Its witness method uses diagonal Schur extensions.
"""
from dataclasses import dataclass
from itertools import combinations
from cyclic_symmetric_family import witness as diagonal_witness
from quadratic_centroid import independent,zero_combinations
from quadratic_target import affine_domain,apply_basis,evaluate_anf,insert,reduce_vector
from raw_symmetric_section import recover as symmetric_section


def _outer(r,v):
    return sum((v if (v>>j)&1 else 0)<<(j*r) for j in range(r))


def _diag(r,a):
    return sum(((a>>(j*(r+1)))&1)<<j for j in range(r))


def _minor_rows(r,basis):
    d=len(basis)
    pairs=tuple(combinations(range(d),2))
    entries=[[sum(((a>>(i+r*j))&1)<<k for k,a in enumerate(basis))
              for j in range(r)] for i in range(r)]
    def multiply(a,b):
        value=a&b
        for k,(i,j) in enumerate(pairs,d):
            value|=((((a>>i)&(b>>j))^((a>>j)&(b>>i)))&1)<<k
        return value
    rows={}
    sides=tuple(combinations(range(r),2))
    for i,j in sides:
        for k,l in sides:
            minor=multiply(entries[i][k],entries[j][l])^multiply(entries[i][l],entries[j][k])
            insert(minor,0,rows)
    return rows,pairs


def rank_one_matrices(r,basis):
    if r<1:
        raise ValueError("invalid matrix dimension")
    basis=tuple(basis)
    if (any(not 0<=a<1<<(r*r) or any(((a>>(i+r*j))^(a>>(j+r*i)))&1
                                      for i,j in combinations(range(r),2)) for a in basis)
            or len(independent(basis))!=len(basis)):
        raise ValueError("expected an independent symmetric matrix basis")
    # Remove purely linear consequences of the minor equations, then compute
    # minors again in the surviving coordinates. This can only shrink dimension.
    while basis:
        d=len(basis)
        rows,pairs=_minor_rows(r,basis)
        cuts=[v for i,(v,_) in rows.items() if i<d]
        if not cuts:
            break
        _,kernel,_=affine_domain(d,((v,0) for v in cuts))
        basis=tuple(apply_basis(basis,x) for x in kernel)
    if not basis:
        return ()
    # Every quadratic product of two coordinate functions must reduce to a
    # linear representative. Diagonal products already satisfy X_i²=X_i.
    products=[[1<<i if i==j else 0 for j in range(d)] for i in range(d)]
    for k,(i,j) in enumerate(pairs,d):
        v,_=reduce_vector(1<<k,rows)
        if v>>d:
            return None
        products[i][j]=products[j][i]=v
    # On a true point p the transpose of multiplication by X_i sends p to
    # p_i*p. Split into its 0/1 eigenvectors; invalid algebras may fail here.
    groups=[tuple(1<<j for j in range(d))]
    for i in range(d):
        cols=tuple(sum(((z>>j)&1)<<k for k,z in enumerate(products[i]))
                   for j in range(d))
        refined=[]
        for group in groups:
            zero=zero_combinations(group,lambda x:apply_basis(cols,x))
            one=zero_combinations(group,lambda x:apply_basis(cols,x)^x)
            if len(zero)+len(one)!=len(group):
                return None
            refined.extend(c for c in (zero,one) if c)
        groups=refined
    if any(len(g)!=1 for g in groups):
        return None
    result=[]
    for (point,) in groups:
        matrix=apply_basis(basis,point)
        v=_diag(r,matrix)
        if not v or matrix!=_outer(r,v):
            return None
        result.append(matrix)
    return tuple(result)


@dataclass
class LocusChart:
    n: int
    r: int
    anf: tuple
    section: object
    points: tuple
    diagonal: tuple
    axes: tuple

    def witness(self,target):
        if not 0<=target<1<<self.r:
            raise ValueError("invalid binary output")
        return diagonal_witness(self.n,self.r,self.anf,self.section,self.diagonal,self.axes,target)


def prepare(n,r,constant,linear,pairs,*,max_trials=1,section=None):
    anf=constant,tuple(linear),dict(pairs)
    if section is None:
        section=symmetric_section(n,r,*anf,max_trials=max_trials)
    if section is None:
        return None
    raw=lambda x:evaluate_anf(*anf,x)
    leaves=section.leaves
    if len(leaves)!=r or len(independent(leaves))!=r or any(not 0<v<1<<n for v in leaves):
        return None
    def polar(x,y):
        return constant^raw(x)^raw(y)^raw(x^y)
    if any(polar(x,y) for x,y in combinations(leaves,2)):
        return None
    basis=independent(sum(polar(1<<i,l)<<(j*r) for j,l in enumerate(leaves)) for i in range(n))
    points=rank_one_matrices(r,basis)
    if points is None:
        return None
    chosen=independent(_diag(r,D) for D in points)
    if len(chosen)!=r:
        return None
    # Dualize the range basis: w_j.v_i=delta_ij. These are leaf coordinates.
    axes=tuple(apply_basis(leaves,affine_domain(r,((v,int(i==j)) for i,v in enumerate(chosen)))[0])
               for j in range(r))
    return LocusChart(n,r,anf,section,points,tuple(_outer(r,v) for v in chosen),axes)


def check():
    from random import Random
    from hidden_product_network import encoder
    from quadratic_target import interpolate
    rng=Random(90812)
    def dense(d):
        b=[1<<i for i in range(d)]
        for _ in range(10*d):
            i,j=rng.sample(range(d),2)
            b[i]^=b[j]
        return b
    accepted=0
    for _ in range(130):
        r=4
        mats=[]
        for j in range(rng.randrange(1,8)):
            if rng.randrange(2):
                a=_outer(r,rng.randrange(1,1<<r))
            else:
                a=0
                for i in range(r):
                    for k in range(i+1):
                        if rng.randrange(2):
                            a|=(1<<(i*r+k))|(1<<(k*r+i))
            mats.append(a)
        mats=independent(mats)
        result=rank_one_matrices(r,mats)
        if result is not None:
            values={apply_basis(mats,x) for x in range(1,1<<len(mats))}
            assert set(result)=={v for v in values if v==_outer(r,_diag(r,v))}
            accepted+=1
    # The full space Sym_2 has three generators but its single minor does
    # not reduce all quadratic coordinate products to linear representatives.
    assert rank_one_matrices(2,(1,6,8)) is None
    for r in (7,8,10):
        n=2*r+1
        ib,ob=dense(n),dense(r)
        enc=encoder(ib); mask=(1<<r)-1
        drift=[rng.randrange(1<<r) for i in range(n)]
        offset=rng.randrange(1<<n);out_offset=rng.randrange(1<<r)
        def raw(x):
            w=enc(x)^offset
            c,y=w&mask,(w>>r)&mask
            # Off-diagonal complete adjacency = J + I.
            v=(c&y)^((y^((y.bit_count()&1)*mask)) if w>>(2*r) else 0)
            for i in range(r):
                v^=(((c>>i)&(c>>((i+2)%r)))&1)<<((i+1)%r)
            return apply_basis(ob,v)^apply_basis(drift,x)^out_offset
        anf=interpolate(raw,n)
        chart=prepare(n,r,*anf)
        assert chart and chart.section.solution_dimension==1
        expected={_outer(r,v) for v in (*ob,apply_basis(ob,mask))}
        assert set(chart.points)==expected
        for target in [0,1,mask,*rng.choices(range(1<<r),k=4)]:
            assert raw(chart.witness(target))==target
    print(f"{accepted}/130 random loci certified and exhaustively matched; complete overlaps r=7,8,10 and 21 raw witnesses passed")


if __name__=="__main__":
    check()
