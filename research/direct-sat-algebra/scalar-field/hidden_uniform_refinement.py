"""Certified refinement of a homogeneous field form into a simple uniform hypergraph."""
from dataclasses import dataclass
from itertools import combinations
from quadratic_centroid import independent, zero_combinations
from quadratic_target import apply_basis, insert, reduce_vector
from hidden_product_network import encoder
from binomial_inequation import nonzero
from product_network_inequality import trace_dual


def _vertex_frame(f,d,defect):
    # The trace radical, quotient atom and corner-lift calculation is the
    # degree-independent incidence-algebra stage of the quadratic recognizer.
    m,mask=f.m,f.size-1
    n=d*m
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
    return vertices if not rem and len(vertices)==d else None


@dataclass(frozen=True)
class Chart:
    field: object
    frames: tuple
    shift: int
    edges: tuple  # (vertex subset, packed binary output columns)
    output_offset: int

    def raw_input(self,codes):
        value=self.shift
        for code,frame in zip(codes,self.frames):
            value ^= apply_basis(frame,code)
        return value

    def output(self,codes):
        y=self.output_offset
        for edge,frame in self.edges:
            a=1
            for i in edge:
                a=self.field.mul(a,codes[i])
            y ^= apply_basis(frame,a)
        return y


def refine(stage,degree=3):
    f=stage.field
    m,mask=f.m,f.size-1
    n,o=len(stage.domain_basis),len(stage.output_basis)
    d,h=n//m,o//m
    if degree<2 or f.size<=degree or d<degree or not h:
        return None
    def coord(x,j):
        return (x>>(m*j)) & mask
    def scale(x,c):
        val=j=0
        while x:
            if x&mask: val |= f.mul(x&mask,c)<<(m*j)
            j+=1
            x >>= m
        return val
    top=stage.top
    mons=set(top)
    deriv=[]
    for ex,c in top.items():
        if len(ex)!=d or sum(ex)!=degree:
            return None
        for k,v in enumerate(ex):
            if v%2:
                for i in range(d):
                    new=list(ex)
                    new[k]-=1
                    new[i]+=1
                    key=tuple(new)
                    mons.add(key)
                    deriv.append((key,c,i*d+k))
    mons=sorted(mons)
    indices={ex:j for j,ex in enumerate(mons)}
    deriv=[(indices[ex],c,j) for ex,c,j in deriv]
    span={}
    for j in range(h):
        poly=sum(coord(top.get(ex,0),j)<<(m*t) for t,ex in enumerate(mons))
        for b in range(m):
            insert(scale(poly,1<<b),0,span)
    if len(span)!=o:
        return None
    def defect(mat):
        out=[0]*len(mons)
        for t,c,j in deriv:
            a=coord(mat,j)
            if a: out[t] ^= scale(c,a)
        return sum(reduce_vector(sum(coord(v,j)<<(m*t) for t,v in enumerate(out)),span)[0]
                   << (j*m*len(mons)) for j in range(h))
    vertices=_vertex_frame(f,d,defect)
    if vertices is None:
        return None
    frames=tuple(tuple(stage.raw_input(scale(v,1<<j)) for j in range(m)) for v in vertices)
    flat=tuple(v for fr in frames for v in fr)
    if len(independent(flat))!=n:
        return None
    def raw(x):
        return stage.raw_output(stage.evaluate(stage.input_coordinates(x)))
    def restrict_difference(ids):
        points=[0]
        for i in ids:
            points += [x^frames[i][0] for x in points]
        ans=0
        for x in points: ans ^= raw(x)
        return ans
    edges=[]
    for edge in combinations(range(d),degree):
        coefficient=stage.output_coordinates(restrict_difference(edge))
        if coefficient:
            frame=tuple(stage.raw_output(scale(coefficient,1<<j)) for j in range(m))
            edges.append((edge,frame))
    outcols=tuple(v for _,fr in edges for v in fr)
    if len(outcols)!=o or len(independent(outcols))!=o:
        return None
    outcode=encoder(outcols)
    shifts={}
    for j,(edge,_) in enumerate(edges):
        for v in edge:
            val=coord(outcode(restrict_difference(i for i in edge if i!=v)),j)
            if v in shifts and shifts[v]!=val:
                return None
            shifts[v]=val
    shift=0
    for i,v in shifts.items(): shift ^= apply_basis(frames[i],v)
    result=Chart(f,frames,shift,tuple(edges),raw(shift))
    encode=encoder(flat)
    for k in range(degree+1):
        for subset in combinations(range(n),k):
            x=sum(1<<i for i in subset)
            z=encode(x^shift)
            if result.output([coord(z,i) for i in range(d)])!=raw(x):
                return None
    return result


def recover(n,m,coefficients,d=3):
    from hidden_uniform_field import recover as coordinates
    stage=coordinates(n,m,coefficients,d=d)
    return None if stage is None else refine(stage,d)


def decide(chart,target,predicate,required=1,*,max_degree=3):
    """Decide one raw Boolean ANF bit. Its dictionary uses monomial masks as keys."""
    if required not in (0,1) or max_degree<0 or target<0:
        raise ValueError("invalid bit, target or degree")
    f=chart.field
    m,arity=f.m,len(chart.frames)
    n=m*arity
    active=[]
    for mon,c in predicate.items():
        if not 0<=mon<1<<n or c not in (0,1) or mon.bit_count()>max_degree:
            raise ValueError("invalid bounded-degree Boolean predicate")
        if c: active.append(mon)
    outcols=tuple(v for _,frame in chart.edges for v in frame)
    pivots={}
    for i,v in enumerate(outcols): insert(v,1<<i,pivots)
    rem,goal=reduce_vector(target^chart.output_offset,pivots)
    if rem:
        return False
    zero=(0,)*arity
    equations=[]
    for j,(edge,_) in enumerate(chart.edges):
        ex=tuple(int(i in edge) for i in range(arity))
        equations.append(((1,ex),((goal>>(m*j))&(f.size-1),zero)))
    degree=max((mon.bit_count() for mon in active),default=0)
    flat=tuple(v for fr in chart.frames for v in fr)
    values={}
    for k in range(degree+1):
        for subset in combinations(range(n),k):
            y=sum(1<<j for j in subset)
            x=chart.shift^apply_basis(flat,y)
            values[y]=(1^required^(sum((x&mon)==mon for mon in active)&1))
    # Binary subset Mobius inversion, valid on the downward-closed prefix.
    for j in range(n):
        bit=1<<j
        for y in values:
            if y&bit:
                values[y] ^= values[y^bit]
    dual=trace_dual(f)
    traces=[]
    for j in range(n):
        c=dual[j%m]
        terms=[]
        for k in range(m):
            ex=list(zero)
            ex[j//m]=1<<k
            terms.append((tuple(ex),c))
            c=f.mul(c,c)
        traces.append(terms)
    poly={}
    for mon,on in values.items():
        if not on: continue
        p={zero:1}
        for j in range(n):
            if not (mon>>j)&1: continue
            nxt={}
            for ex,c in p.items():
                for row,v in traces[j]:
                    idx=tuple(1+(a+b-1)%(f.size-1) if a+b else 0 for a,b in zip(ex,row))
                    nxt[idx]=nxt.get(idx,0)^f.mul(c,v)
            p={ex:c for ex,c in nxt.items() if c}
        for ex,c in p.items():
            poly[ex]=poly.get(ex,0)^c
    return nonzero(f,arity,equations,[(c,ex) for ex,c in poly.items() if c])
