"""Field-coordinate recovery from the full top derivative of a binary ANF.

recover(n,m,coefficients,d=3) takes {squarefree bit mask: packed output}.
It returns a polynomial-basis module chart or None. Chart.top and Chart.terms
use standard K exponent tuples and concatenated output-field chunks. Terms
include the constant and any compatible lower-degree drift. The input ANF
is certified at every binary monomial of degree at most d. For fixed d all
steps cost polynomial bit work; q>d is required for the scaling interpolation.
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations,combinations_with_replacement,product
from punctured_chart import TableField,coordinates
from punctured_chart_witness import power_chart
from quadratic_centroid import independent
from quadratic_target import apply_basis,insert,reduce_vector
from untwisted_field_coordinates import module_basis,scale
from extension_field_target import pack,unpack
from affine_binomial import power


def masks(n,k):
    for positions in combinations(range(n),k):
        yield sum(1<<j for j in positions)


def centroid(n,m,co,d):
    # T(e_i,J) is zero on repeated basis arguments. Its value on distinct
    # arguments is the squarefree degree-d coefficient, with no factorial.
    tails=list(masks(n,d-1))
    columns=[tuple(0 if J&(1<<i) else co.get(J|(1<<i),0) for J in tails)
             for i in range(n)]
    flat=[v for col in columns for v in col]
    if len(independent(flat))!=m:
        return None
    packed=[pack(col,m) for col in columns]
    if len(independent(packed))!=n:
        return None
    # T(S e_i,J)=D T(e_i,J) suffices in every slot by symmetry. Keep all
    # repeated-first tests. Omitting them admits spurious input operators.
    width=m*len(tails)
    defects=[col<<(i*width) for i in range(n) for col in packed]
    for j in range(m):
        membership=pack(((v>>j)&1 for v in flat),m)
        defects.extend(membership<<i for i in range(m))
    pivots={}
    kernel=[]
    for k,v in enumerate(defects):
        rem,z=reduce_vector(v,pivots)
        if rem:
            pivots[rem.bit_length()-1]=rem,z^(1<<k)
        else:
            kernel.append(z^(1<<k))
    return [(unpack(v,n),unpack(v>>(n*n),m)) for v in kernel]


def frames(n,m,actions):
    k=len(actions)
    if k<2 or n%k or m%k:
        return None
    ident=pack((1<<i for i in range(m)),m)
    basis=independent((ident,*(pack(t,m) for _,t in actions)))
    if len(basis)!=k:
        return None
    pair={pack(t,m):s for s,t in actions}
    pair[ident]=tuple(1<<i for i in range(n))
    enc=coordinates(basis)
    actions=[(pair[v],unpack(v,m)) for v in basis]
    table=[]
    for s,t in actions:
        row=[]
        for u,v in actions:
            z=enc(pack((apply_basis(t,x) for x in v),m))
            if any(apply_basis(s,x)!=apply_basis([a[i] for a,_ in actions],z)
                   for i,x in enumerate(u)):
                return None
            row.append(z)
        table.append(tuple(row))
    algebra=TableField(tuple(table))
    if not algebra.certify():
        return None
    iso=power_chart(k,1,algebra.mul)
    def build(index,dim):
        matrices=[pack(action[index],dim) for action in actions]
        return module_basis(dim,[unpack(apply_basis(matrices,z),dim) for z in iso.basis])
    domain,out=build(0,n),build(1,m)
    return None if domain is None or out is None else (iso.field,domain,out)


def ordinary_value(f,terms,x):
    result=0
    for ex,c in terms.items():
        value=1
        for i,k in enumerate(ex):
            if k:
                value=f.mul(value,power(f,(x>>(i*f.m))&(f.size-1),k))
        result ^= scale(f,value,c)
    return result


def simplex_coefficients(f,V,d,value):
    # Tensor divided differences on the lower simplex, then expand Newton
    # products prod_{l<k}(X-alpha_l) into ordinary monomials. alpha_l=l.
    newton=[[1]]
    weights=[]
    for k in range(d+1):
        w=[]
        for j in range(k+1):
            den=1
            for l in range(k+1):
                if l!=j: den=f.mul(den,j^l)
            w.append(f.inverse(den))
        weights.append(w)
        ns=[0]*(k+2)
        for i,c in enumerate(newton[-1]):
            ns[i]^=f.mul(c,k)
            ns[i+1]^=c
        newton.append(ns)
    result={}
    for t in range(d+1):
        for pos in combinations_with_replacement(range(V),t):
            ex=[0]*V
            for i in pos: ex[i]+=1
            support=sorted(set(pos))
            terms=list(product(*(range(ex[i]+1) for i in support)))
            coefficient=0
            for js in terms:
                w=1
                x=0
                for i,j in zip(support,js):
                    w=f.mul(w,weights[ex[i]][j])
                    x|=j<<(f.m*i)
                coefficient ^=scale(f,w,value(x))
            if coefficient:
                for js in terms:
                    w=1
                    key=[0]*V
                    for i,j in zip(support,js):
                        key[i]=j
                        w=f.mul(w,newton[ex[i]][j])
                    key=tuple(key)
                    result[key]=result.get(key,0)^scale(f,w,coefficient)
    return {e:c for e,c in result.items() if c}


@dataclass
class Chart:
    field: object
    domain_basis: tuple
    output_basis: tuple
    top: dict
    terms: dict
    raw_coefficients: dict
    input_coordinates: object
    output_coordinates: object

    def raw_input(self,x):
        return apply_basis(self.domain_basis,x)

    def raw_output(self,y):
        return apply_basis(self.output_basis,y)

    def evaluate(self,x):
        return ordinary_value(self.field,self.terms,x)

    def homogeneous(self,x):
        return ordinary_value(self.field,self.top,x)


def recover(n,m,coefficients,d=3):
    if (type(d) is not int or d<2 or min(n,m)<0 or any(type(a) is not int or
            a<0 or a.bit_length()>n or type(v) is not int or v<0 or v.bit_length()>m or
            (v and a.bit_count()>d) for a,v in coefficients.items())):
        raise ValueError("invalid bounded-degree binary ANF")
    if n<d or not m:
        return None
    co={a:v for a,v in coefficients.items() if v}
    acts=centroid(n,m,co,d)
    data=frames(n,m,acts) if acts else None
    if data is None:
        return None
    f,domain,out=data
    if f.size<=d:
        return None
    ix,iy=coordinates(domain),coordinates(out)
    def raw(x):
        v=0
        for a,c in co.items():
            if (a&x)==a: v^=c
        return v
    @lru_cache(None)
    def value(x):
        return iy(raw(apply_basis(domain,x)))
    lagrange=[]
    for j in range(d+1):
        den=1
        for k in range(d+1):
            if k!=j: den=f.mul(den,k^j)
        lagrange.append(f.inverse(den))
    @lru_cache(None)
    def homogeneous(x):
        y=0
        for lam,weight in enumerate(lagrange):
            y^=scale(f,weight,value(scale(f,lam,x)))
        return y
    V=n//f.m
    top=simplex_coefficients(f,V,d,homogeneous)
    if any(sum(e)!=d for e in top):
        return None
    low=simplex_coefficients(f,V,d-1,lambda x:value(x)^homogeneous(x))
    chart=Chart(f,domain,out,top,{**top,**low},co,ix,iy)
    # An ordinary K monomial of degree <=d has binary degree <=d under
    # binary coordinate maps. Values on this entire downset determine its ANF.
    for size in range(d+1):
        for x in masks(n,size):
            if raw(x)!=chart.raw_output(chart.evaluate(ix(x))):
                return None
    return chart


def self_test():
    from punctured_witness import BinaryField
    from random import Random
    rng=Random(883)
    def rb(n):
        cols=()
        while len(cols)<n:
            cols=independent((*cols,rng.randrange(1<<n)))
        return cols
    def anf(n,d,fn):
        result={}
        for k in range(d+1):
            for x in masks(n,k):
                y=fn(x)
                s=x
                while s:
                    s=(s-1)&x
                    if s!=x: y^=result.get(s,0)
                if y: result[x]=y
        return result
    for mod,V,edges in [(7,3,[(0,1,2)]),(11,4,[(0,1,2),(0,2,3)]),
                        (11,4,[(0,1,2,3)])]:
        old=BinaryField(mod)
        k=old.m
        d=len(edges[0])
        n,m=k*V,k*len(edges)
        ib,ob=rb(n),rb(m)
        sh,oc=rng.randrange(1,1<<n),rng.randrange(1,1<<m)
        def raw(x):
            z=apply_basis(ib,x^sh)
            v=[(z>>(j*k))&(old.size-1) for j in range(V)]
            y=0
            for j,edge in enumerate(edges):
                c=1
                for i in edge: c=old.mul(c,v[i])
                # Allow repeated-coordinate top terms and lower K-degree drift.
                c ^= power(old,v[0],d)^old.mul(v[0],v[1])^v[-1]
                y|=c<<(j*k)
            return apply_basis(ob,y)^oc
        co=anf(n,d,raw)
        chart=recover(n,m,co,d)
        assert chart is not None and chart.field.m==k and chart.raw_coefficients==co
        for x in (range(1<<n) if n<=7 else (rng.randrange(1<<n) for _ in range(100))):
            z=chart.input_coordinates(x)
            assert chart.raw_input(z)==x and chart.raw_output(chart.evaluate(z))==raw(x)
            a=rng.randrange(1<<k)
            assert chart.homogeneous(scale(chart.field,a,z))==scale(
                chart.field,power(chart.field,a,d),chart.homogeneous(z))
        print(f"GF(2^{k}) degree {d} dense {len(edges)}-edge chart verified")
    old=BinaryField(11)
    def incompatible(x):
        u,v,w=[(x>>(3*i))&7 for i in range(3)]
        return old.mul(old.mul(u,v),w)^power(old,u,4)
    assert recover(9,3,anf(9,3,incompatible)) is None


if __name__=="__main__":
    self_test()
