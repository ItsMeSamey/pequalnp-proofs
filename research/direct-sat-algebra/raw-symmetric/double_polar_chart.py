"""Reconstruct and verify a scalar field quadratic on a binary slice.

recover(n,m,c,linear,pairs) takes only the restricted packed ANF. The binary
embedding, image constraints, output encoding and a full scalar quadratic
(including affine terms) are exposed. None means no chart was certified.
"""
from dataclasses import dataclass
from itertools import combinations
from quadratic_centroid import independent,zero_combinations
from quadratic_target import affine_domain,apply_basis,evaluate_anf,interpolate,insert,reduce_vector
from punctured_chart import coordinates
from bounded_punctured_chart import complete


def chunks(v,m,d):
    return tuple((v>>(m*i))&((1<<m)-1) for i in range(d))


def pack(v,m):
    return sum(a<<(m*i) for i,a in enumerate(v))


@dataclass
class Chart:
    field: object
    output_basis: tuple
    embedding: tuple
    normals: tuple
    gram: tuple
    diagonal: tuple
    linear: tuple
    constant: int  # in field coordinates

    def ambient_value(self,z):
        f=self.field
        zs=chunks(z,f.m,len(self.gram))
        v=self.constant
        for i,x in enumerate(zs):
            v ^= f.mul(self.linear[i],x)^f.mul(self.diagonal[i],f.mul(x,x))
            for j in range(i):
                v ^= f.mul(self.gram[j][i],f.mul(zs[j],x))
        return apply_basis(self.output_basis,v)

    def homogeneous(self,target):
        """Return (ScalarForm, field target, shifted binary pins, shift).

        A homogeneous witness y maps back by chart.lift(y ^ shift).
        """
        from scalar_field_pins import ScalarForm
        f=self.field
        d=len(self.gram)
        rows={}
        for i in range(d):
            for j in range(f.m):
                col=pack([f.mul(1<<j,self.gram[i][k]) for k in range(d)],f.m)
                insert(col,1<<(i*f.m+j),rows)
        rem,shift=reduce_vector(pack(self.linear,f.m),rows)
        if rem:
            raise ArithmeticError("nondegenerate Gram misses translation")
        field_target=coordinates(self.output_basis)(target^self.ambient_value(shift))
        pins=tuple((v,(v&shift).bit_count()%2) for v in self.normals)
        cross={(i,j):self.gram[i][j] for i,j in combinations(range(d),2)}
        return ScalarForm(f,self.diagonal,cross),field_target,pins,shift

    def lift(self,z):
        return coordinates(self.embedding)(z)


def gram_coordinates(gram,f):
    """Represent each Gram column in a greedily selected K-column basis."""
    n=len(gram)
    rows={}
    chosen=[]
    embedding=[]
    for i,vec in enumerate(gram):
        residual=list(vec)
        coords=[0]*n
        for j in sorted(rows):
            v,label=rows[j]
            c=residual[j]
            if c:
                residual=[a^f.mul(c,b) for a,b in zip(residual,v)]
                coords=[a^f.mul(c,b) for a,b in zip(coords,label)]
        pivot=next((j for j,a in enumerate(residual) if a),None)
        if pivot is not None:
            scale=f.inverse(residual[pivot])
            k=len(chosen)
            chosen.append(i)
            coords[k]=1
            rows[pivot]=([f.mul(scale,a) for a in residual],[f.mul(scale,a) for a in coords])
            coords=[0]*n
            coords[k]=1
        embedding.append(pack(coords,f.m))
    return chosen,tuple(embedding)


def linear_data(n,m,linear,pairs,field,output_basis, *, projected=False):
    enc=coordinates(output_basis)
    gram=tuple(tuple(enc(pairs.get(tuple(sorted((i,j))),0)) for i in range(n))
               for j in range(n))
    selected,embedding=gram_coordinates(gram,field)
    d=len(selected)
    if not d or d%2 or (not projected and len(independent(embedding))!=n):
        return None
    subgram=tuple(tuple(gram[i][j] for j in selected) for i in selected)
    zs=[chunks(z,m,d) for z in embedding]
    def cross(z):
        v=0
        for i,j in combinations(range(d),2):
            v ^= field.mul(subgram[i][j],field.mul(z[i],z[j]))
        return v
    return embedding,subgram,tuple(enc(l)^cross(z) for l,z in zip(linear,zs))


def fit(n,m,constant,linear,pairs,field,output_basis, *, projected=False):
    data=linear_data(n,m,linear,pairs,field,output_basis,projected=projected)
    if data is None:
        return None
    embedding,subgram,values=data
    d=len(subgram)
    zs=[chunks(z,m,d) for z in embedding]
    enc=coordinates(output_basis)
    rhs=pack(values,m)
    # Field-linear coefficients of z_i^2 and z_i contribute binary-linearly.
    rows={}
    for k in range(2*d):
        coords=[z[k%d] for z in zs]
        if k<d:
            coords=[field.mul(x,x) for x in coords]
        for j in range(m):
            col=pack([field.mul(1<<j,x) for x in coords],m)
            insert(col,1<<(k*m+j),rows)
    rem,solution=reduce_vector(rhs,rows)
    if rem:
        return None
    ds=chunks(solution,m,2*d)
    normals=tuple(affine_domain(m*d,((z,0) for z in embedding))[1])
    graph=Chart(field,output_basis,embedding,normals,subgram,ds[:d],ds[d:],enc(constant))
    # Equality on degree <= 2 tests the whole map. This also verifies that
    # quotient coordinates did not discard an unmodeled term.
    recovered=interpolate(lambda x:graph.ambient_value(apply_basis(embedding,x)),n)
    goal=(constant,list(linear),{e:v for e,v in pairs.items() if v})
    return graph if recovered==goal else None


def polar_field(n,m,constant,linear,pairs):
    if (min(n,m,constant)<0 or len(linear)!=n or any(v<0 or v.bit_length()>m for v in
            (constant,*linear,*pairs.values())) or any(not 0<=i<j<n for i,j in pairs)):
        raise ValueError("invalid packed ANF")
    ij=next((e for e,v in pairs.items() if v),None)
    if ij is None:
        return None
    unit=tuple(1<<i for i in range(n))
    rows=[tuple(pairs.get(tuple(sorted((i,j))),0) for j in range(n)) for i in range(n)]
    def b(x,y):
        return apply_basis([apply_basis(row,y) for row in rows],x)
    def perp(plane):
        return zero_combinations(unit,lambda x:pack([b(x,y) for y in plane],m))
    p,r=(1<<i for i in ij)
    P=perp(perp((p,)))
    R=perp(perp((r,)))
    lp=tuple(b(x,r) for x in P)
    lr=tuple(b(p,y) for y in R)
    if (len(independent(lp))!=len(lp) or len(independent(lr))!=len(lr)
            or len(lp)>m or len(lr)>m):
        return None
    e=b(p,r)
    cross=tuple(tuple(b(x,y) for y in R) for x in P)
    result=complete(m,lp,lr,cross,known_unit=e)
    if result is None:
        return None
    field,output_basis,_,_=result
    return field,output_basis


def recover(n,m,constant,linear,pairs):
    geometry=polar_field(n,m,constant,linear,pairs)
    return fit(n,m,constant,linear,pairs,*geometry) if geometry is not None else None


def self_test():
    from random import Random
    from punctured_witness import BinaryField
    rng=Random(862)
    def random_basis(n):
        b=()
        while len(b)<n:
            b=independent((*b,rng.randrange(1,1<<n)))
        return b
    # Binary pin masks mix the coordinates of all four field variables.
    for m,d,mod,h in ((7,4,131,1),(13,2,8219,2)):
        f=BinaryField(mod)
        N=m*d
        masks=[]
        while len(masks)<h:
            a=rng.randrange(1,1<<N)
            if all(chunks(a,m,d)) and len(independent([*masks,a]))>len(masks):
                masks.append(a)
        offset,base,_=affine_domain(N,[(v,rng.randrange(2)) for v in masks])
        n=N-h
        ib,ob=random_basis(n),random_basis(m)
        shift,out=rng.randrange(1<<n),rng.randrange(1<<m)
        squares=[rng.randrange(1<<m) for _ in range(d)]
        def hidden(x):
            z=chunks(offset^apply_basis(base,apply_basis(ib,x^shift)),m,d)
            y=0
            for i in range(0,d,2):
                y ^= f.mul(z[i],z[i+1])
            for a,v in zip(squares,z):
                y ^= f.mul(a,f.mul(v,v))
            return out^apply_basis(ob,y)
        anf=interpolate(hidden,n)
        chart=recover(n,m,*anf)
        assert chart is not None and len(chart.gram)==d and len(chart.normals)==h
        for x in [0,*[rng.randrange(1<<n) for _ in range(60)]]:
            z=apply_basis(chart.embedding,x)
            assert chart.lift(z)==x and chart.ambient_value(z)==hidden(x)
        target=hidden(0)
        form,t,pins,delta=chart.homogeneous(target)
        for x in [0,*[rng.randrange(1<<n) for _ in range(20)]]:
            y=apply_basis(chart.embedding,x)^delta
            assert all((a&y).bit_count()%2==b for a,b in pins)
            assert (form.evaluate(y)==t)==(hidden(x)==target)
        if d>2*h:
            for goal in (0,1,37):
                form,t,pins,delta=chart.homogeneous(goal)
                y=form.plane_witness(t,pins)
                assert hidden(chart.lift(y^delta))==goal
        print(f"GF(2^{m}), dimension {d}, {h} hidden correlated pins certified")


if __name__=="__main__":
    self_test()
