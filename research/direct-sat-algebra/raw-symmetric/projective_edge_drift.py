"""Solve verified binary-field bidegree-(1,1) equations with a field witness.

solve(f,n,edges) accepts (i,j,a,b,c,d) for a*x_i*x_j+b*x_i+c*x_j+d=0.
Loops, repeated edges, unary equations and zero coefficients are allowed.
Return a tuple of field elements or None if UNSAT. Input coordinates are
supplied or independently verified, and arbitrary cross-vertex drifts are
outside this method. All running times are polynomial in input size and m.
"""
from itertools import combinations
from field_plane_root import rational_roots,trim
from gain_target import binary_solution

ONE=(1,0,0,1)


def compose(f,M,N):
    a,b,c,d=M
    e,g,h,k=N
    return (f.mul(a,e)^f.mul(b,h),f.mul(a,g)^f.mul(b,k),
            f.mul(c,e)^f.mul(d,h),f.mul(c,g)^f.mul(d,k))


def inverse(M):
    a,b,c,d=M
    return d,b,c,a


def action(f,M,x):
    a,b,c,d=M
    top,bot=(a,c) if x is None else (f.mul(a,x)^b,f.mul(c,x)^d)
    return None if not bot else f.mul(top,f.inverse(bot))


def solve(f,n,edges):
    edges=tuple(edges)
    if type(n) is not int or n<0:
        raise ValueError("invalid vertex count")
    adj=[[] for _ in range(n)]
    splits=[]
    for i,j,a,b,c,d in edges:
        if not (0<=i<n and 0<=j<n and all(0<=z<f.size for z in (a,b,c,d))):
            raise ValueError("invalid field edge")
        if f.mul(a,d)^f.mul(b,c):
            M=(b,d,a,c)
            adj[i].append((j,M))
            adj[j].append((i,inverse(M)))
        elif a:
            inv=f.inverse(a)
            splits.append(((i,f.mul(c,inv)),(j,f.mul(b,inv))))
        elif b:
            splits.append(((i,f.mul(d,f.inverse(b))),))
        elif c:
            splits.append(((j,f.mul(d,f.inverse(c))),))
        elif d:
            return None

    owner=[-1]*n
    frame=[None]*n
    domains=[]
    default=[]
    for root in range(n):
        if owner[root]>=0:
            continue
        k=len(domains)
        owner[root],frame[root]=k,ONE
        forbidden=set()
        allowed=None
        stack=[root]
        while stack:
            i=stack.pop()
            pole=action(f,inverse(frame[i]),None)
            if pole is not None:
                forbidden.add(pole)
            for j,M in adj[i]:
                U=compose(f,M,frame[i])
                if owner[j]<0:
                    owner[j],frame[j]=k,U
                    stack.append(j)
                else:
                    A,B,C,D=compose(f,inverse(frame[j]),U)
                    eq=trim((B,A^D,C))
                    if eq:
                        if allowed is None:
                            allowed=set(rational_roots(f,eq))
                        else:
                            allowed={t for t in allowed if B^f.mul(A^D,t)^f.mul(C,f.mul(t,t))==0}
        if allowed is not None:
            allowed-=forbidden
            if not allowed:
                return None
            choice=min(allowed)
        else:
            if len(forbidden)==f.size:
                return None
            choice=next(t for t in range(len(forbidden)+1) if t not in forbidden)
        domains.append((allowed,forbidden))
        default.append(choice)

    atoms={}
    groups=[[] for _ in domains]
    units=set()
    positive=[]
    for clause in splits:
        ids=[]
        for i,val in clause:
            k=owner[i]
            t=action(f,inverse(frame[i]),val)
            allowed,forbidden=domains[k]
            if t is None or t in forbidden or (allowed is not None and t not in allowed):
                continue
            atom=(k,t)
            if atom not in atoms:
                atoms[atom]=len(atoms)
                groups[k].append(atoms[atom])
            ids.append(atoms[atom])
        if not ids:
            return None
        if len(set(ids))==1:
            units.add(ids[0])
        else:
            positive.append(tuple(sorted(ids)))
    relations={}
    for ids in groups:
        for i,j in combinations(ids,2):
            relations[i,j]={(0,0),(1,0),(0,1)}
    for i,j in positive:
        if (i,j) in relations:
            relations[i,j].discard((0,0))
        else:
            relations[i,j]={(0,1),(1,0),(1,1)}
    truth=binary_solution([{1} if i in units else {0,1} for i in range(len(atoms))],relations)
    if truth is None:
        return None
    for (k,t),i in atoms.items():
        if truth[i]:
            default[k]=t
    values=tuple(action(f,frame[i],default[owner[i]]) for i in range(n))
    if any(x is None for x in values):
        raise ArithmeticError("projective root maps to infinity")
    for i,j,a,b,c,d in edges:
        x,y=values[i],values[j]
        if f.mul(a,f.mul(x,y))^f.mul(b,x)^f.mul(c,y)^d:
            raise ArithmeticError("lifted witness failed edge equation")
    return values


def fit_chart(field,input_frames,input_shift,endpoints,output_basis,constant,linear,pairs):
    """Recognize endpoint-local coefficients in supplied invertible raw coordinates.

    input_frames has one m-column frame per vertex. output_basis is a flat
    sequence of m columns per edge. Output translations are absorbed into d.
    Returns a RawChart or None when the named bidegree model cannot fit.
    """
    from field_rank_drift import field_solve
    from hidden_product_network import encoder
    from quadratic_target import apply_basis,evaluate_anf,interpolate
    input_frames=tuple(tuple(v) for v in input_frames)
    endpoints=tuple(endpoints)
    output_basis=tuple(output_basis)
    n,m=len(input_frames)*field.m,len(endpoints)*field.m
    raw_basis=tuple(v for fr in input_frames for v in fr)
    if (len(linear)!=n or len(output_basis)!=m or any(len(fr)!=field.m for fr in input_frames)
            or any(not 0<=v<1<<n for v in (*raw_basis,input_shift))
            or any(not 0<=v<1<<m for v in (*output_basis,constant,*linear,*pairs.values()))
            or any(not 0<=i<j<n for i,j in pairs)
            or any(not 0<=v<len(input_frames) for edge in endpoints for v in edge)):
        raise ValueError("invalid raw chart")
    encoder(raw_basis)
    decode=encoder(output_basis)
    raw_anf=(constant,tuple(linear),dict(pairs))
    def target_values(z):
        return decode(evaluate_anf(*raw_anf,input_shift^apply_basis(raw_basis,z)))
    samples=[0]+[1<<j for j in range(n)]+[(1<<i)|(1<<j) for i,j in combinations(range(n),2)]
    values=list(map(target_values,samples))
    def chunk(z,i):
        return (z>>(i*field.m))&(field.size-1)
    rows=[]
    for k,(i,j) in enumerate(endpoints):
        eqs=[]
        for s,v in zip(samples,values):
            x,y=chunk(s,i),chunk(s,j)
            eqs.append(((field.mul(x,y),x,y,1),chunk(v,k)))
        coeff=field_solve(field,eqs,4)
        if coeff is None:
            return None
        rows.append((i,j,*coeff))
    def replay(z):
        v=0
        for k,(i,j,a,b,c,d) in enumerate(rows):
            x,y=chunk(z,i),chunk(z,j)
            v|=(field.mul(a,field.mul(x,y))^field.mul(b,x)^field.mul(c,y)^d)<<(k*field.m)
        return v
    if interpolate(target_values,n)!=interpolate(replay,n):
        return None
    return RawChart(field,tuple(rows),raw_basis,input_shift,output_basis,raw_anf)


from dataclasses import dataclass


@dataclass(frozen=True)
class RawChart:
    field: object
    rows: tuple
    inputs: tuple
    shift: int
    outputs: tuple
    anf: tuple

    def solve(self,target):
        from hidden_product_network import encoder
        from quadratic_target import apply_basis,evaluate_anf
        if not 0<=target<1<<len(self.outputs):
            raise ValueError("invalid raw output target")
        goal=encoder(self.outputs)(target)
        f=self.field
        adjusted=[(i,j,a,b,c,d^((goal>>(e*f.m))&(f.size-1)))
                  for e,(i,j,a,b,c,d) in enumerate(self.rows)]
        xs=solve(f,len(self.inputs)//f.m,adjusted)
        if xs is None:
            return None
        x=self.shift^apply_basis(self.inputs,sum(v<<(k*f.m) for k,v in enumerate(xs)))
        if evaluate_anf(*self.anf,x)!=target:
            raise ArithmeticError("raw witness failed original ANF")
        return x


def check():
    from itertools import product
    from random import Random
    from punctured_witness import BinaryField
    from quadratic_target import apply_basis,interpolate
    from hidden_product_network import encoder
    rng=Random(2295)
    checked=0
    for mod in (7,11):
        f=BinaryField(mod)
        for _ in range(140):
            n=rng.randrange(1,5)
            edges=[]
            for j in range(rng.randrange(9)):
                i,k=rng.randrange(n),rng.randrange(n)
                a,b,c,d=rng.choices(range(f.size),k=4)
                if j%2 and a:
                    d=f.mul(f.mul(b,c),f.inverse(a))
                edges.append((i,k,a,b,c,d))
            def sat(v):
                return all(not(f.mul(a,f.mul(v[i],v[j]))^f.mul(b,v[i])^f.mul(c,v[j])^d)
                           for i,j,a,b,c,d in edges)
            truth=any(sat(v) for v in product(range(f.size),repeat=n))
            witness=solve(f,n,edges)
            assert (witness is not None)==truth and (witness is None or sat(witness))
            checked+=1
    f=BinaryField(7)
    assert solve(f,4,[(i,i+1,1,0,0,t) for i,t in enumerate((1,0,1))]) is None
    edges=[]
    prefix=ONE
    for i,pole in enumerate(range(f.size)):
        b=action(f,prefix,pole)
        assert b is not None
        edges.append((i,i+1,1,0,b,1))
        prefix=compose(f,(0,1,1,b),prefix)
        assert (solve(f,i+2,edges) is not None)==(i+2<=f.size)
    def dense(n):
        b=[1<<j for j in range(n)]
        for _ in range(10*n):
            i,j=rng.sample(range(n),2)
            b[i]^=b[j]
        return tuple(b)
    ib,ob=dense(8),dense(8)
    frames=tuple(ib[i:i+2] for i in range(0,8,2))
    enc=encoder(ib)
    endpoints=[(0,1),(1,2),(2,3),(3,0)]
    def raw(x):
        z=enc(x^139)
        p=[(z>>(2*i))&3 for i in range(4)]
        y=0
        for e,(i,j) in enumerate(endpoints):
            y|=(f.mul(p[i],p[j])^f.mul(1+(e%3),p[i])^p[j])<<(2*e)
        return 94^apply_basis(ob,y)
    anf=interpolate(raw,8)
    chart=fit_chart(f,frames,139,endpoints,ob,*anf)
    assert chart
    image={raw(x) for x in range(256)}
    for t in range(256):
        w=chart.solve(t)
        assert (w is not None)==(t in image) and (w is None or raw(w)==t)
    def hostile(x):
        z=enc(x^139)
        return raw(x)^apply_basis(ob,(z>>4)&3)
    assert fit_chart(f,frames,139,endpoints,ob,*interpolate(hostile,8)) is None
    print(f"{checked} mixed-rank brute comparisons, 256 raw targets, path and hostile drift controls passed")


if __name__=="__main__":
    check()
