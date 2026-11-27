"""Graph reconstruction from a verified field-quadratic coordinate chart."""
from itertools import combinations
from hidden_product_network import Chart, encoder
from quadratic_centroid import independent, zero_combinations
from quadratic_target import affine_domain, insert, interpolate, reduce_vector


def refine(stage):
    f=stage.field
    m,mask=f.m,f.size-1
    n,outbits=len(stage.domain_basis),len(stage.output_basis)
    d,h=n//m,outbits//m
    if m==1 or not d or not h or n%m or outbits%m:
        return None
    def coord(x,j):
        return (x>>(m*j)) & mask
    def scale(x,c):
        out=j=0
        while x:
            if x & mask: out |= f.mul(x&mask,c)<<(m*j)
            j+=1
            x >>= m
        return out
    def action(mat,x):
        out=0
        for j in range(d):
            if coord(x,j):
                out ^= scale((mat>>(n*j)) & ((1<<n)-1),coord(x,j))
        return out
    def compose(a,b):
        return sum(action(a,(b>>(n*j)) & ((1<<n)-1))<<(n*j) for j in range(d))

    mons=[(i,i) for i in range(d)] + list(combinations(range(d),2))
    coeff=list(stage.squares)+[stage.cross.get(key,0) for key in mons[d:]]
    span={}
    for j in range(h):
        comp=sum(coord(v,j)<<(m*t) for t,v in enumerate(coeff))
        for bit in range(m):
            insert(scale(comp,1<<bit),0,span)
    if len(span)!=h*m:
        return None
    def defect(mat):
        deriv=[0]*len(mons)
        for t,(i,j) in enumerate(mons):
            for (u,v),c in stage.cross.items():
                a=0
                if i==u: a ^= coord(mat,j*d+v)
                if i==v: a ^= coord(mat,j*d+u)
                if j!=i:
                    if j==u: a ^= coord(mat,i*d+v)
                    if j==v: a ^= coord(mat,i*d+u)
                if a: deriv[t] ^= scale(c,a)
        result=0
        for j in range(h):
            poly=sum(coord(v,j)<<(m*t) for t,v in enumerate(deriv))
            result |= reduce_vector(poly,span)[0]<<(j*m*len(mons))
        return result
    algebra=zero_combinations((1<<j for j in range(n*d)),defect)
    space={}
    for a in algebra: insert(a,0,space)
    one=sum(1<<(m*j+n*j) for j in range(d))
    if reduce_vector(one,space)[0] or any(reduce_vector(compose(a,b),space)[0]
                                          for a in algebra for b in algebra):
        return None
    def trace_pair(a,b):
        val=0
        for i in range(d):
            for j in range(d):
                x,y=coord(a,i*d+j),coord(b,j*d+i)
                if x and y: val ^= f.mul(x,y)
        return val
    rad=zero_combinations(algebra,lambda a:sum(trace_pair(a,b)<<(j*m)
                                               for j,b in enumerate(algebra)))
    rad_rows={}
    for a in rad: insert(a,0,rad_rows)
    def quotient(a):
        return reduce_vector(a,rad_rows)[0]
    if any(quotient(compose(a,b)) or quotient(compose(b,a)) for a in rad for b in algebra):
        return None
    qb=independent(quotient(a) for a in algebra)
    center=zero_combinations(qb,lambda a:sum(
        quotient(compose(a,b)^compose(b,a))<<(j*n*d) for j,b in enumerate(qb)))
    fixed=zero_combinations(center,lambda a:quotient(compose(a,a)^a))
    atoms=[quotient(one)]
    for a in fixed:
        new=[]
        for b in atoms:
            part=quotient(compose(a,b))
            new.extend(v for v in (part,b^part) if v)
        atoms=new
    vertices=[]
    rem=one
    for atom in atoms:
        a=compose(rem,compose(atom,rem))
        for _ in range((d-1).bit_length()):
            a=compose(a,a)
        if quotient(a)!=atom or compose(a,a)!=a or compose(rem,a)!=a or compose(a,rem)!=a:
            return None
        rem ^= a
        pivots={}
        for j in range(d):
            col=(a>>(n*j))&((1<<n)-1)
            if reduce_vector(col,pivots)[0]:
                vertices.append(col)
                for bit in range(m): insert(scale(col,1<<bit),0,pivots)
    if rem or len(vertices)!=d:
        return None
    frames=tuple(tuple(stage.raw_input(scale(v,1<<j)) for j in range(m)) for v in vertices)
    flat=tuple(v for fr in frames for v in fr)
    if len(independent(flat))!=n:
        return None
    def homogeneous(x):
        result=0
        for (u,v),c in zip(mons,coeff):
            z=f.mul(coord(x,u),coord(x,v))
            if z: result ^= scale(c,z)
        return result
    if any(homogeneous(x) for x in vertices):
        return None
    edges=[]
    for i,j in combinations(range(d),2):
        c=homogeneous(vertices[i]^vertices[j])
        if c:
            frame=tuple(stage.raw_output(scale(c,1<<k)) for k in range(m))
            edges.append((i,j,0,frame))
    output_cols=[v for _,_,_,fr in edges for v in fr]
    if len(output_cols)!=outbits or len(independent(output_cols))!=outbits:
        return None
    def raw(x):
        return stage.raw_output(stage.evaluate(stage.input_coordinates(x)))
    def polar(x,y):
        return raw(0)^raw(x)^raw(y)^raw(x^y)
    equations=[]
    for v in flat:
        discrepancy=raw(v)^raw(0)
        cols=[polar(v,1<<j) for j in range(n)]
        for b in range(outbits):
            equations.append((sum(((x>>b)&1)<<j for j,x in enumerate(cols)),(discrepancy>>b)&1))
    origin=affine_domain(n,equations)
    if origin is None:
        return None
    shift=origin[0]
    graph=Chart(f,frames,shift,tuple(edges),raw(shift))
    encode_graph=encoder(flat)
    def replay(x):
        z=encode_graph(x^shift)
        return graph.output([coord(z,i) for i in range(d)])
    return graph if interpolate(raw,n)==interpolate(replay,n) else None


def recover(n,outbits,constant,linear,pairs):
    from untwisted_field_coordinates import recover as field_coordinates
    stage=field_coordinates(n,outbits,constant,linear,pairs)
    return None if stage is None else refine(stage)
