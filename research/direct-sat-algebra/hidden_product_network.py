"""Recover a densely binary-affine-recoded network of twisted field products.

recover(n,outbits,constant,linear,pairs) accepts packed squarefree vector ANF
and returns a verified Chart, or None if recognition was inconclusive. Guaranteed
on the separated simple-graph promise: for every ordered vertex pair i!=k, k
has a neighbor outside {i} union N(i), and there are no isolated vertices.
There is one common field coordinate at each vertex, with independent Frobenius
twists allowed at the two ends of each edge. The output basis may be arbitrary.
"""
from dataclasses import dataclass
from itertools import combinations
from binary_matrix_algebra import cols,product
from field_plane_root import rational_roots
from punctured_chart_witness import power_chart
from punctured_witness import BinaryField
from quadratic_centroid import independent,zero_combinations
from quadratic_target import affine_domain,apply_basis,evaluate_anf,insert,interpolate,reduce_vector


def encoder(basis):
    rows={}
    for i,b in enumerate(basis):
        if not insert(b,1<<i,rows):
            raise ValueError("dependent chart basis")
    def encode(x):
        rest,z=reduce_vector(x,rows)
        if rest:
            raise ValueError("outside chart")
        return z
    return encode


def frob(f,x,t):
    for _ in range(t):
        x=f.mul(x,x)
    return x


@dataclass(frozen=True)
class Chart:
    field: object
    frames: tuple
    shift: int
    edges: tuple  # (left vertex,right vertex,right twist,ambient output basis)
    output_offset: int

    def raw_input(self,codes):
        if len(codes)!=len(self.frames) or any(not 0<=a<self.field.size for a in codes):
            raise ValueError("invalid vertex field coordinates")
        x=self.shift
        for a,frame in zip(codes,self.frames):
            x^=apply_basis(frame,a)
        return x

    def output(self,codes):
        if len(codes)!=len(self.frames) or any(not 0<=a<self.field.size for a in codes):
            raise ValueError("invalid vertex field coordinates")
        v=self.output_offset
        for i,j,t,frame in self.edges:
            v^=apply_basis(frame,self.field.mul(codes[i],frob(self.field,codes[j],t)))
        return v

    def edge_targets(self,target):
        z=encoder(tuple(v for _,_,_,frame in self.edges for v in frame))(target^self.output_offset)
        return tuple((z>>(i*self.field.m))&(self.field.size-1) for i in range(len(self.edges)))


def derivation_space(n,outbits,pairs):
    """Eliminate the forced output action T by representing all B_ij in an output basis."""
    ij=tuple(combinations(range(n),2))
    image=[pairs.get(e,0) for e in ij]
    base=independent(image)
    if len(base)!=outbits:
        return None
    encode=encoder(base)
    coords=list(map(encode,image))
    selected=[image.index(y) for y in base]
    polar=tuple(tuple(pairs.get(tuple(sorted((i,j))),0) for j in range(n)) for i in range(n))
    def defect(s):
        actions=cols(n,s)
        rhs=[apply_basis(polar[j],actions[i])^apply_basis(polar[i],actions[j]) for i,j in ij]
        images=[rhs[j] for j in selected]
        return sum((v^apply_basis(images,c))<<(k*outbits) for k,(v,c) in enumerate(zip(rhs,coords)))
    derivations=zero_combinations((1<<i for i in range(n*n)),defect)
    return tuple(derivations),polar


def _field_frames(n,planes,derivations):
    m=len(planes[0])
    if m==1:
        # BinaryField's modulus validator targets extension degrees >=2.
        class PrimeField(BinaryField):
            def __init__(self):
                self.m,self.size,self.modulus,self.trace_mask=1,2,3,1
        return PrimeField(),tuple(tuple(p) for p in planes)
    local=[]
    for plane in planes:
        encode=encoder(plane)
        # Evaluation at the first nonzero vertex vector identifies its scalar
        # algebra with its vertex space. Store the action for every basis image.
        action_rows={}
        restriction=[]
        for s in derivations:
            mat=cols(n,s)
            small=tuple(encode(apply_basis(mat,x)) for x in plane)
            packed=sum(v<<(m*i) for i,v in enumerate(small))
            insert(small[0],packed,action_rows)
            restriction.append(packed)
        if len(action_rows)!=m or len(independent(restriction))!=m:
            return None
        def multiply(a,b):
            rest,mat=reduce_vector(a,action_rows)
            if rest:
                raise ValueError("scalar outside local action")
            return apply_basis(cols(m,mat),b)
        local.append(power_chart(m,1,multiply))
    field=local[0].field
    polynomial=tuple((field.modulus>>i)&1 for i in range(m+1))
    frames=[]
    for plane,chart in zip(planes,local):
        roots=rational_roots(chart.field,polynomial)
        if len(roots)!=m:
            return None
        a=min(roots)
        v=1
        frame=[]
        for _ in range(m):
            frame.append(apply_basis(plane,chart.decode(v)))
            v=chart.field.mul(v,a)
        frames.append(tuple(frame))
    return field,tuple(frames)


def recover(n,outbits,constant,linear,pairs):
    linear=tuple(linear)
    pairs={e:v for e,v in pairs.items() if v}
    if (min(n,outbits,constant)<0 or len(linear)!=n or
            any(not 0<=v<1<<outbits for v in (constant,*linear,*pairs.values())) or
            any(not 0<=i<j<n for i,j in pairs)):
        raise ValueError("invalid vector ANF")
    if not n or not outbits:
        return None
    data=derivation_space(n,outbits,pairs)
    if data is None:
        return None
    derivations,polar=data
    if any(product(n,s,t)!=product(n,t,s) for s,t in combinations(derivations,2)):
        return None
    projectors=zero_combinations(derivations,lambda s:product(n,s,s)^s)
    unit=tuple(1<<i for i in range(n))
    planes=[unit]
    for s in projectors:
        mat=cols(n,s)
        refined=[]
        for plane in planes:
            image0=zero_combinations(plane,lambda x:apply_basis(mat,x))
            image1=zero_combinations(plane,lambda x:apply_basis(mat,x)^x)
            if len(image0)+len(image1)!=len(plane):
                return None
            refined.extend(v for v in (image0,image1) if v)
        planes=refined
    if not planes or len(derivations)!=n or len({len(p) for p in planes})!=1:
        return None
    try:
        local=_field_frames(n,planes,derivations)
    except ValueError:
        return None
    if local is None:
        return None
    field,frames=local
    m=field.m
    def B(x,y):
        out=0
        for i in range(n):
            if (x>>i)&1:
                out^=apply_basis(polar[i],y)
        return out
    if any(B(u,v) for p in frames for u,v in combinations(p,2)):
        return None
    edges=[]
    for i,j in combinations(range(len(frames)),2):
        left,right=frames[i],frames[j]
        values=tuple(tuple(B(u,v) for v in right) for u in left)
        if not any(any(row) for row in values):
            continue
        output=tuple(row[0] for row in values)
        if len(independent(output))!=m:
            return None
        twist=next((t for t in range(m) if all(
            apply_basis(output,field.mul(1<<a,frob(field,1<<b,t)))==values[a][b]
            for a in range(m) for b in range(m))),None)
        if twist is None:
            return None
        edges.append((i,j,twist,output))
    outcols=tuple(v for _,_,_,frame in edges for v in frame)
    if len(outcols)!=outbits or len(independent(outcols))!=outbits:
        return None
    # The canonical product vanishes on a single vertex. Therefore the
    # centered supplied value on each recovered basis vector is B(shift,x).
    equations=[]
    for p in frames:
        for x in p:
            discrepancy=evaluate_anf(0,linear,pairs,x)
            columns=[B(x,y) for y in unit]
            for b in range(outbits):
                equations.append((sum(((v>>b)&1)<<j for j,v in enumerate(columns)),(discrepancy>>b)&1))
    solution=affine_domain(n,equations)
    if solution is None:
        return None
    shift=solution[0]
    chart=Chart(field,frames,shift,tuple(edges),evaluate_anf(constant,linear,pairs,shift))
    enc=encoder(tuple(v for frame in frames for v in frame))
    def evaluate(x):
        z=enc(x^shift)
        return chart.output(tuple((z>>(m*i))&(field.size-1) for i in range(len(frames))))
    if interpolate(evaluate,n)!=(constant,list(linear),pairs):
        return None
    return chart


def check():
    from random import Random
    rng=Random(729)
    def basis(d):
        vals=()
        while len(vals)<d:
            vals=independent((*vals,rng.randrange(1<<d)))
        return vals
    for modulus in (7,11):
        f=BinaryField(modulus)
        nv=5
        m=f.m
        n=o=nv*m
        ib,ob=basis(n),basis(o)
        translation,offset=rng.randrange(1<<n),rng.randrange(1<<o)
        twist=[(i%m,(2*i+1)%m) for i in range(nv)]
        scales=[rng.randrange(1,f.size) for _ in range(nv)]
        def hidden(x):
            z=apply_basis(ib,x^translation)
            code=[(z>>(m*i))&(f.size-1) for i in range(nv)]
            y=0
            for i,(a,b) in enumerate(twist):
                u=frob(f,code[i],a)
                v=frob(f,code[(i+1)%nv],b)
                y|=f.mul(scales[i],f.mul(u,v))<<(m*i)
            return offset^apply_basis(ob,y)
        c,l,q=interpolate(hidden,n)
        chart=recover(n,o,c,l,q)
        assert chart is not None and len(chart.frames)==5 and len(chart.edges)==5
        for _ in range(130):
            codes=[rng.randrange(f.size) for _ in chart.frames]
            v=chart.output(codes)
            assert hidden(chart.raw_input(codes))==v
            assert chart.edge_targets(v)==tuple(chart.field.mul(codes[i],frob(chart.field,codes[j],a))
                                                for i,j,a,_ in chart.edges)
        # The shift and offset are unique because the full polar radical vanishes.
        assert (chart.shift,chart.output_offset)==(translation,offset)
        # Change one raw linear coefficient with an output discrepancy outside
        # all possible input translations. Full polar/edge recognition still fits.
        incompatible=list(l)
        incompatible[0]^=1
        assert recover(n,o,c,incompatible,q) is None
    # Degree-six simple graph on seven vertices, all determinant edges.
    # The globally simultaneous E12,E21 induce T=0 and do not commute.
    nv=7
    edges=tuple(combinations(range(nv),2))
    q={}
    for t,(i,j) in enumerate(edges):
        q[2*i,2*j+1]=1<<t
        q[2*i+1,2*j]=1<<t
    assert recover(2*nv,len(edges),0,[0]*(2*nv),q) is None
    print("F4/F8 translated twisted dense C5 charts, 260 raw witnesses and three negative controls passed")


if __name__=="__main__":
    check()
