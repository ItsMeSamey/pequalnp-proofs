"""Recover densely recoded restricted field products for m>3h, h=2m-n.

A successful chart certifies the entire input map, including an arbitrary
output translation. Projected adjoints outside the promised dimension bound
are rejected. For m<=3h use small_target() to count and witness directly.
"""
from dataclasses import dataclass
from punctured_chart import TableField,coordinates,projected_adjoints
from quadratic_centroid import independent,zero_combinations
from quadratic_target import apply_basis,evaluate_anf,reduce_vector,insert,affine_domain,interpolate


@dataclass
class Chart:
    field: object
    output_basis: tuple
    left: tuple
    right: tuple
    left_images: tuple
    right_images: tuple
    output_offset: int
    # Binary masks on field coordinates. RHS = parity(mask & 1).
    left_normals: tuple
    right_normals: tuple

    def lift(self,u,v):
        return (apply_basis(self.left,coordinates(self.left_images)(u^1)) ^
                apply_basis(self.right,coordinates(self.right_images)(v^1)))


def small_target(n,m,constant,linear,pairs,target):
    """Exact fallback only for the branch m<=3h, n<=5h."""
    h=2*m-n
    if h<2 or m>3*h or n<0:
        raise ValueError("outside the small-dimension branch")
    hits=0
    witness=None
    for x in range(1<<n):
        if evaluate_anf(constant,linear,pairs,x)==target:
            hits+=1
            if witness is None:
                witness=x
    return hits,witness


def rows_for(basis):
    rows={}
    for v in basis:
        insert(v,0,rows)
    return rows


def complete(m,lp,lr,cross, *, known_unit=None, product=False):
    """Complete a partial product and check the field and every supplied pair."""
    enc_l,enc_r=coordinates(lp),coordinates(lr)
    rows=rows_for(lr)
    common=zero_combinations(lp,lambda x:reduce_vector(x,rows)[0])
    common_rows=rows_for(common)
    def mu(x,y):
        return apply_basis([apply_basis(row,enc_r(y)) for row in cross],enc_l(x))
    matrices=[]
    unit=known_unit
    standard=[1<<i for i in range(m)]
    for x in common:
        kernel=zero_combinations(common,lambda y:reduce_vector(mu(x,y),common_rows)[0])
        # Extend a map from dependent source/output sample pairs while
        # checking every relation, then evaluate it on the standard basis.
        equations={}
        for b in kernel:
            xb=mu(x,b)
            for c in common:
                arg,val=mu(b,c),mu(xb,c)
                rem,label=reduce_vector(arg,equations)
                if rem:
                    equations[rem.bit_length()-1]=rem,val^label
                elif label!=val:
                    return None
        if len(equations)!=m:
            return None
        matrix=tuple(reduce_vector(s,equations)[1] for s in standard)
        if unit is None:
            if len(independent(matrix))!=m:
                return None
            unit=coordinates(matrix)(x)
        matrices.append(matrix)
    if not unit or (known_unit is None and any(reduce_vector(unit,rows_for(h))[0]==0 for h in (lp,lr))):
        return None
    def pack(matrix):
        return sum(v<<(m*i) for i,v in enumerate(matrix))
    def unpack(v):
        return tuple((v>>(m*i))&((1<<m)-1) for i in range(m))
    algebra=independent(pack([apply_basis(a,col) for col in b])
                        for a in matrices for b in matrices)
    if len(algebra)!=m:
        return None
    columns=[apply_basis(unpack(A),unit) for A in algebra]
    if len(independent(columns))!=m:
        return None
    alg_coords=coordinates(columns)
    basis=independent((unit,*standard))
    encode=coordinates(basis)
    table=[]
    for z in basis:
        matrix=unpack(apply_basis(algebra,alg_coords(z)))
        table.append(tuple(encode(apply_basis(matrix,y)) for y in basis))
    field=TableField(tuple(table))
    if not field.certify(product=product):
        return None
    li,ri=tuple(map(encode,lp)),tuple(map(encode,lr))
    if any(field.mul(x,y)!=encode(cross[i][j]) for i,x in enumerate(li)
           for j,y in enumerate(ri)):
        return None
    return field,basis,li,ri


def recover(n,m,constant,linear,pairs):
    h=2*m-n
    if (min(n,m,constant)<0 or len(linear)!=n or any(v<0 or v.bit_length()>m for v in
            (constant,*linear,*pairs.values())) or any(not 0<=i<j<n for i,j in pairs)):
        raise ValueError("invalid packed ANF")
    if h<2 or m<=3*h:
        return None
    adj=projected_adjoints(n,m,pairs)
    if len(adj)>2*h:
        return None
    def centered(x):
        return evaluate_anf(0,linear,pairs,x)
    def polar(x,y):
        return centered(x)^centered(y)^centered(x^y)
    for k in range(1,1<<len(adj)):
        v=apply_basis(adj,k)
        cols=[(v>>(i*n))&((1<<n)-1) for i in range(n)]
        if any(apply_basis(cols,x)!=x for x in cols):
            continue
        p=independent(cols)
        r=independent(x^(1<<i) for i,x in enumerate(cols))
        if max(len(p),len(r))>=m or any(polar(x,y) for u in (p,r) for x in u for y in u):
            continue
        lp,lr=tuple(map(centered,p)),tuple(map(centered,r))
        if len(independent(lp))!=len(p) or len(independent(lr))!=len(r):
            continue
        cross=[[polar(x,y) for y in r] for x in p]
        result=complete(m,lp,lr,cross)
        if result is None:
            continue
        field,basis,li,ri=result
        def normals(u):
            return tuple(affine_domain(m,((x,0) for x in u))[1])
        return Chart(field,basis,p,r,li,ri,constant^basis[0],normals(li),normals(ri))
    return None


def self_test():
    from random import Random
    from punctured_witness import BinaryField
    rng=Random(914)
    field=BinaryField(1033)
    n,m=17,10
    def random_basis(d):
        basis=()
        while len(basis)<d:
            basis=independent((*basis,rng.randrange(1,1<<d)))
        return basis
    p=affine_domain(m,[(1,0)])[1]
    r=affine_domain(m,[(3,0),(6,0)])[1]
    for dense in (False,True):
        ib=random_basis(n) if dense else [1<<i for i in range(n)]
        ob=random_basis(m) if dense else [1<<i for i in range(m)]
        shift,offset=(rng.randrange(1<<n),rng.randrange(1<<m)) if dense else (0,0)
        def original(x):
            z=apply_basis(ib,x^shift)
            a=1^apply_basis(p,z&511)
            b=1^apply_basis(r,z>>9)
            return apply_basis(ob,field.mul(a,b))^offset
        data=interpolate(original,n)
        chart=recover(n,m,*data)
        assert chart and chart.output_offset==offset
        assert sorted((len(chart.left_normals),len(chart.right_normals)))==[1,2]
        frame=(*chart.left,*chart.right)
        def rebuilt(z):
            d=len(chart.left)
            u=1^apply_basis(chart.left_images,z&((1<<d)-1))
            v=1^apply_basis(chart.right_images,z>>d)
            assert chart.lift(u,v)==apply_basis(frame,z)
            assert all(((a&u).bit_count()&1)==(a&1) for a in chart.left_normals)
            assert all(((a&v).bit_count()&1)==(a&1) for a in chart.right_normals)
            return apply_basis(chart.output_basis,chart.field.mul(u,v))^chart.output_offset
        assert interpolate(rebuilt,n)==interpolate(lambda z:original(apply_basis(frame,z)),n)
        for _ in range(100):
            z=rng.randrange(1<<n)
            assert rebuilt(z)==original(apply_basis(frame,z))
    assert small_target(2,2,0,[1,2],{},3)==(1,3)
    assert recover(n,m,0,[0]*n,{}) is None
    print("degree-ten (1,2) codimensions, plain/dense affine charts and small fallback passed")


if __name__=="__main__":
    self_test()
