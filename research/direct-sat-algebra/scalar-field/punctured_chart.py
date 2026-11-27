"""Recognize hidden field multiplication restricted to two punctured hyperplanes.

Use packed binary squarefree ANF. Output translation may be recovered on request. The field has
identity 1 in a general binary vector basis (the first vector is the recovered unit).
"""
from dataclasses import dataclass
from quadratic_centroid import independent, zero_combinations
from quadratic_target import affine_domain,apply_basis,evaluate_anf,interpolate,reduce_vector,insert
from punctured_witness import BinaryField


def coordinates(basis):
    rows={}
    for i,v in enumerate(basis):
        insert(v,1<<i,rows)
    def encode(y):
        rem,coords=reduce_vector(y,rows)
        if rem:
            raise ValueError("outside chart coordinates")
        return coords
    return encode


class TableField(BinaryField):
    """General binary vector basis with first element equal to one."""
    def __init__(self,table):
        self.table=table
        self.m=len(table)
        self.size=1<<self.m

    def mul(self,a,b):
        return apply_basis([apply_basis(row,b) for row in self.table],a)

    def certify(self, *, product=False):
        units=[1<<j for j in range(self.m)]
        if any(self.mul(1,x)!=x for x in units):
            return False
        for x in units:
            for y in units:
                if self.mul(x,y)!=self.mul(y,x):
                    return False
                for z in units:
                    if self.mul(self.mul(x,y),z)!=self.mul(x,self.mul(y,z)):
                        return False
        # Finite reduced commutative algebras are products of fields. Bijective
        # squaring excludes nilpotents. Fixed dimension counts field factors.
        squares=[self.mul(x,x) for x in units]
        if len(independent(squares))!=self.m:
            return False
        if product:
            return True
        if len(independent(a^b for a,b in zip(units,squares)))!=self.m-1:
            return False
        self.trace_mask=sum(self._trace(x)<<j for j,x in enumerate(units))
        return True


@dataclass
class Chart:
    field: object
    output_basis: tuple
    left: tuple
    right: tuple
    left_images: tuple
    right_images: tuple
    trace_a: int
    trace_b: int
    output_offset: int


def candidate_units(lp,lr,mixed,m):
    if m==2:
        return (1,2,3)
    left=coordinates(lp)
    right=coordinates(lr)
    def mu(x,y):
        return apply_basis([apply_basis(row,right(y)) for row in mixed],left(x))
    rows={}
    for y in lr:
        insert(y,0,rows)
    inter=zero_combinations(lp,lambda x:reduce_vector(x,rows)[0])
    if not inter:
        return ()
    x=inter[0]
    if len(inter)<m-1:
        # On H_left + H_right, commutativity determines multiplication by x.
        basis=independent((*lr,*lp))
        products=[mu(x,y) if not reduce_vector(y,rows)[0] else mu(y,x) for y in basis]
    else:
        # Associativity extends multiplication by x to one point off H.
        usable=zero_combinations(lr,lambda y:reduce_vector(mu(x,y),rows)[0])
        if not usable:
            return ()
        b=usable[0]
        c=next((v for v in lr if reduce_vector(mu(b,v),rows)[0]),None)
        if c is None:
            return ()
        basis=(*lr,mu(b,c))
        products=[mu(x,y) for y in lr]+[mu(mu(x,b),c)]
    if len(independent(products))!=m:
        return ()
    return (apply_basis(basis,coordinates(products)(x)),)


def projected_adjoints(n,m,pairs):
    polars=[tuple(pairs.get(tuple(sorted((i,j))),0) for i in range(n)) for j in range(n)]
    def pack(cols,width):
        return sum(v<<(width*i) for i,v in enumerate(cols))
    def matrix(v):
        return tuple((v>>(i*n))&((1<<n)-1) for i in range(n))
    def defects(v):
        s=matrix(v)
        a=matrix(v>>(n*n))
        return pack([apply_basis(polars[j],s[i]) ^ apply_basis(polars[i],a[j])
                     for i in range(n) for j in range(n)],m)
    adjoints=zero_combinations((1<<i for i in range(2*n*n)),defects)
    projected=independent(v&((1<<(n*n))-1) for v in adjoints)
    return projected


def recover(n,m,constant,linear,pairs, *, unknown_output_shift=False):
    if m<2 or n!=2*(m-1) or (not constant and not unknown_output_shift):
        return None
    if (len(linear)!=n or any(v<0 or v.bit_length()>m for v in
            (constant,*linear,*pairs.values())) or any(not 0<=i<j<n for i,j in pairs)):
        raise ValueError("invalid squarefree ANF")
    projected=projected_adjoints(n,m,pairs)
    def matrix(v):
        return tuple((v>>(i*n))&((1<<n)-1) for i in range(n))
    if len(projected)>4:
        return None
    axes=[]
    for mask in range(1,1<<len(projected)):
        s=matrix(apply_basis(projected,mask))
        plane=independent(s)
        if len(plane)==m-1 and all(apply_basis(s,x)==x for x in s):
            axes.append(plane)
    def centered(x):
        return evaluate_anf(0,linear,pairs,x)
    def polar(x,y):
        return centered(x)^centered(y)^centered(x^y)
    for p in axes:
        for r in axes:
            if len(independent((*p,*r)))!=n:
                continue
            if any(polar(x,y) for plane in (p,r) for x in plane for y in plane):
                continue
            lp=tuple(map(centered,p))
            lr=tuple(map(centered,r))
            if len(independent(lp))!=m-1 or len(independent(lr))!=m-1:
                continue
            cross=tuple(tuple(polar(x,y) for y in r) for x in p)
            units=candidate_units(lp,lr,cross,m) if unknown_output_shift else (constant,)
            for unit in units:
                lb=(unit,*lp)
                rb=(unit,*lr)
                if len(independent(lb))!=m or len(independent(rb))!=m:
                    continue
                enc=coordinates(lb)
                rec=coordinates(rb)
                mixed=[rb]+[(u,*row) for u,row in zip(lp,cross)]
                table=tuple(tuple(enc(apply_basis(row,rec(y))) for y in lb) for row in mixed)
                field=TableField(table)
                if not field.certify():
                    continue
                li=tuple(map(enc,lp))
                ri=tuple(map(enc,lr))
                def trace_label(space):
                    x,_,_=affine_domain(m,[(field.trace_row(1),1)]+[
                        (field.trace_row(v),0) for v in space])
                    return x
                # Axis affine terms and every mixed polarization are matched by
                # construction; within-axis polars were checked above.
                return Chart(field,lb,p,r,li,ri,trace_label(li),trace_label(ri),constant^unit)
    return None


def self_test():
    from random import Random
    from punctured_witness import witness
    rng=Random(932)
    def random_basis(d):
        basis=()
        while len(basis)<d:
            basis=independent((*basis,rng.randrange(1,1<<d)))
        return basis
    cases=0
    for m,mod in ((2,7),(3,11),(4,19),(5,37)):
        f=BinaryField(mod)
        n=2*(m-1)
        for same in (False,True):
            _,p,_=affine_domain(m,[(1,0)])
            _,r,_=affine_domain(m,[(1 if same else 3,0)])
            ib,ob=random_basis(n),random_basis(m)
            for dense_shift,offset in [(0,0),(0,ob[0]),(rng.randrange(1<<n),rng.randrange(1<<m))]:
                def original(x):
                    z=apply_basis(ib,x^dense_shift)
                    u=1^apply_basis(p,z&((1<<(m-1))-1))
                    v=1^apply_basis(r,z>>(m-1))
                    return offset^apply_basis(ob,f.mul(u,v))
                c,l,q=interpolate(original,n)
                chart=recover(n,m,c,l,q,unknown_output_shift=bool(offset))
                assert chart is not None,(m,same,offset)
                frame=(*chart.left,*chart.right)
                for z in range(1<<n):
                    u=1^apply_basis(chart.left_images,z&((1<<(m-1))-1))
                    v=1^apply_basis(chart.right_images,z>>(m-1))
                    predicted=chart.output_offset^apply_basis(chart.output_basis,chart.field.mul(u,v))
                    assert predicted==original(apply_basis(frame,z))
                assert chart.output_offset==offset
                for target in range(1<<m):
                    t=coordinates(chart.output_basis)(target^chart.output_offset)
                    pair=witness(chart.field,chart.trace_a,chart.trace_b,t)
                    if pair is None:
                        assert target==offset
                    else:
                        u,v=pair
                        x=(apply_basis(chart.left,coordinates(chart.left_images)(u^1))^
                           apply_basis(chart.right,coordinates(chart.right_images)(v^1)))
                        assert original(x)==target
                cases+=1
    print(f"{cases} dense charts, all inputs and all targets verified")


if __name__=="__main__":
    self_test()
