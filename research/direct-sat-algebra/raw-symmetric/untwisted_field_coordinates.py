"""Recover scalar field and module coordinates of a binary vector quadratic.

Connected untwisted field-product graphs have a full nondegenerate polar
with common scalar field as centroid. No separating-neighbor assumption is
needed. A successful chart certifies a field-module quadratic with affine
K-linear drift; graph recognition is separate. Field chunks are packed
least-significant first. None means the certificate did not succeed.
"""
from dataclasses import dataclass
from itertools import combinations
from extension_field_target import centroid,pack,unpack
from punctured_chart import TableField,coordinates
from punctured_chart_witness import power_chart
from quadratic_centroid import independent
from quadratic_target import apply_basis,evaluate_anf,insert,interpolate,reduce_vector


def scale(f,a,y):
    result=offset=0
    while y:
        result |= f.mul(a,y&(f.size-1))<<offset
        y >>= f.m
        offset += f.m
    return result


@dataclass
class Chart:
    field: object
    domain_basis: tuple
    output_basis: tuple
    squares: tuple
    cross: dict
    linear: tuple
    constant: int
    input_coordinates: object
    output_coordinates: object

    def raw_input(self,x):
        return apply_basis(self.domain_basis,x)

    def raw_output(self,y):
        return apply_basis(self.output_basis,y)

    def homogeneous(self,x):
        f=self.field
        z=[(x>>(i*f.m))&(f.size-1) for i in range(len(self.squares))]
        result=0
        for i,c in enumerate(self.squares):
            result ^= scale(f,f.mul(z[i],z[i]),c)
        for (i,j),c in self.cross.items():
            result ^= scale(f,f.mul(z[i],z[j]),c)
        return result

    def evaluate(self,x):
        f=self.field
        y=self.constant^self.homogeneous(x)
        for i,c in enumerate(self.linear):
            y ^= scale(f,(x>>(i*f.m))&(f.size-1),c)
        return y


def module_basis(d,actions):
    rows={}
    basis=[]
    for i in range(d):
        if not reduce_vector(1<<i,rows)[0]:
            continue
        for a in actions:
            x=a[i]
            if not insert(x,0,rows):
                return None
            basis.append(x)
    return tuple(basis) if len(basis)==d else None


def recover(n,m,constant,linear,pairs):
    if (min(n,m,constant)<0 or len(linear)!=n or any(v<0 or v.bit_length()>m for v in
            (constant,*linear,*pairs.values())) or any(not 0<=i<j<n for i,j in pairs)):
        raise ValueError("invalid packed binary ANF")
    if not n or not m:
        return None
    actions=centroid(n,m,pairs)
    if actions is None or len(actions)<2:
        return None
    k=len(actions)
    if n%k or m%k:
        return None
    ident=pack((1<<i for i in range(n)),n) | (pack((1<<j for j in range(m)),m)<<(n*n))
    basis=independent([ident,*[pack(s,n)|(pack(t,m)<<(n*n)) for s,t in actions]])
    if len(basis)!=k:
        return None
    abstract=coordinates(basis)
    def decode(v):
        return unpack(v,n),unpack(v>>(n*n),m)
    mats=[decode(v) for v in basis]
    def compose(i,j):
        s,t=mats[i]
        u,v=mats[j]
        return pack((apply_basis(s,x) for x in u),n)|(pack((apply_basis(t,x) for x in v),m)<<(n*n))
    table=TableField(tuple(tuple(abstract(compose(i,j)) for j in range(k)) for i in range(k)))
    if not table.certify():
        return None
    canonical=power_chart(k,1,table.mul)
    f=canonical.field
    polynomial_actions=[decode(apply_basis(basis,a)) for a in canonical.basis]
    domain=module_basis(n,[s for s,t in polynomial_actions])
    output=module_basis(m,[t for s,t in polynomial_actions])
    if domain is None or output is None:
        return None
    encode_x,encode_y=coordinates(domain),coordinates(output)
    c=encode_y(constant)
    def centered(x):
        return encode_y(evaluate_anf(0,linear,pairs,apply_basis(domain,x)))
    alpha=2
    inv=f.inverse(f.mul(alpha,alpha)^alpha)
    def homogeneous(x):
        return scale(f,inv,centered(scale(f,alpha,x))^scale(f,alpha,centered(x)))
    units=[1<<(i*k) for i in range(n//k)]
    squares=tuple(map(homogeneous,units))
    cross={}
    for i,j in combinations(range(len(units)),2):
        v=homogeneous(units[i]^units[j])^squares[i]^squares[j]
        if v:
            cross[i,j]=v
    drift=tuple(centered(u)^s for u,s in zip(units,squares))
    chart=Chart(f,domain,output,squares,cross,drift,c,encode_x,encode_y)
    if interpolate(lambda x:chart.raw_output(chart.evaluate(encode_x(x))),n)!=(
            constant,list(linear),{e:v for e,v in pairs.items() if v}):
        return None
    return chart


def self_test():
    from punctured_witness import BinaryField
    from random import Random
    rng=Random(348)
    def rb(d):
        cols=()
        while len(cols)<d:
            cols=independent((*cols,rng.randrange(1,1<<d)))
        return cols
    # A single edge, a triangle, and a claw all violate vertex separation.
    for mod,V,edges in [(7,2,[(0,1)]),(11,3,[(0,1),(1,2),(0,2)]),
                        (19,4,[(0,1),(0,2),(0,3)])]:
        old=BinaryField(mod)
        k=old.m
        n,m=V*k,len(edges)*k
        ib,ob=rb(n),rb(m)
        s,c=rng.randrange(1,1<<n),rng.randrange(1,1<<m)
        def raw(x):
            z=apply_basis(ib,x^s)
            coords=[(z>>(i*k))&(old.size-1) for i in range(V)]
            y=sum(old.mul(coords[i],coords[j])<<(k*l) for l,(i,j) in enumerate(edges))
            return c^apply_basis(ob,y)
        chart=recover(n,m,*interpolate(raw,n))
        assert chart is not None and chart.field.m==k and len(chart.squares)==V
        for x in (range(1<<n) if n<=10 else (rng.randrange(1<<n) for _ in range(150))):
            y=chart.input_coordinates(x)
            assert chart.raw_input(y)==x
            assert chart.evaluate(y)==chart.output_coordinates(raw(x))
            scalar=rng.randrange(chart.field.size)
            assert chart.homogeneous(scale(chart.field,scalar,y))==scale(
                chart.field,chart.field.mul(scalar,scalar),chart.homogeneous(y))
    old=BinaryField(11)
    def quartic(x):
        u,v=x&7,x>>3
        sq=old.mul(u,u)
        return old.mul(u,v)^old.mul(sq,sq)
    assert recover(6,3,*interpolate(quartic,6)) is None
    # Direct product of two scalar fields is a non-field centroid.
    old=BinaryField(7)
    def disconnected(x):
        a,b,c,d=[(x>>(2*i))&3 for i in range(4)]
        return old.mul(a,b)|(old.mul(c,d)<<2)
    assert recover(8,4,*interpolate(disconnected,8)) is None
    print("three dense affine nonseparated graphs, homogeneous scaling, quartic rejection and product-centroid rejection passed")


if __name__=="__main__":
    self_test()
