"""Recognize a hidden binary-affine copy of xy+z over K from its packed ANF.

The pinned decision method handles one-coordinate Frobenius drift after
eliminating z. Inequality is a tuple of raw affine equations: at least one
must fail (None means no inequality). Returns SAT/UNSAT or UNKNOWN for an
unsupported section or exhausted Laurent-term budget. Fixed k extra pins
cost m^O(k) times polynomial bit work; monomial exponents use O(m) bits.
"""
from dataclasses import dataclass
from quadratic_target import affine_domain,apply_basis,evaluate_anf,interpolate,insert,reduce_vector
from quadratic_centroid import independent
from punctured_chart import coordinates
from double_polar_chart import polar_field,linear_data,chunks
from field_rank_drift import field_solve
from affine_binomial import power


def linearized(f,values):
    rows=[]
    for j,v in enumerate(values):
        p=1<<j
        row=[]
        for _ in range(f.m):
            row.append(p)
            p=f.mul(p,p)
        rows.append((row,v))
    return field_solve(f,rows,f.m)


def raw_frame(fn,n):
    base=fn(0)
    return base,tuple(fn(1<<i)^base for i in range(n))


@dataclass
class Slack:
    field: object
    output_basis: tuple
    base: int
    cols: tuple

    def raw(self,x,y,z):
        m=self.field.m
        return self.base^apply_basis(self.cols,x|(y<<m)|(z<<(2*m)))


def prepare(n,m,constant,linear,pairs):
    if (n!=3*m or m<3 or len(linear)!=n or min(constant,*linear,*pairs.values())<0
            or max(constant,*linear,*pairs.values()).bit_length()>m
            or any(not 0<=i<j<n for i,j in pairs)):
        return None
    unit=tuple(1<<i for i in range(n))
    rows={}
    for (i,j),v in pairs.items():
        for b in range(m):
            if v>>b&1:
                rows[i,b]=rows.get((i,b),0)^(1<<j)
                rows[j,b]=rows.get((j,b),0)^(1<<i)
    _,rad,pivots=affine_domain(n,((v,0) for v in rows.values()))
    if len(rad)!=m:
        return None
    q=lambda x:evaluate_anf(constant,linear,pairs,x)
    ri=tuple(q(v)^constant for v in rad)
    if len(independent(ri))!=m:
        return None
    comp=tuple(1<<i for i in pivots)
    data=interpolate(lambda x:q(apply_basis(comp,x)),2*m)
    geometry=polar_field(2*m,m,*data)
    if geometry is None:
        return None
    f,out=geometry
    extracted=linear_data(2*m,m,data[1],data[2],f,out)
    if extracted is None:
        return None
    emb,gram,_=extracted
    if len(gram)!=2:
        return None
    enc=coordinates(out)
    g=gram[0][1]
    xy=tuple((z&((1<<m)-1))|(f.mul(g,z>>m)<<m) for z in emb)
    ix,ir=coordinates(xy),coordinates(ri)
    def decode(w):
        x,y,z=chunks(w,m,3)
        v=apply_basis(comp,ix(x|(y<<m)))
        correction=q(v)^apply_basis(out,z^f.mul(x,y))
        return v^apply_basis(rad,ir(correction))
    base,cols=raw_frame(decode,n)
    if len(independent(cols))!=n:
        return None
    chart=Slack(f,out,base,cols)
    def via_chart(w):
        x,y,z=chunks(w,m,3)
        return apply_basis(out,f.mul(x,y)^z)
    if interpolate(lambda w:q(base^apply_basis(cols,w)),n)!=interpolate(via_chart,n):
        return None
    return chart


def decide(chart,target,pins=(),inequality=None,*,max_terms=None):
    """Search Q(raw)=target under raw parity pins and a vector disequality."""
    f=chart.field
    m=f.m
    mask=f.size-1
    if not 0<=target<f.size or (max_terms is not None and max_terms<0):
        raise ValueError("invalid target or term cap")
    def pull(item):
        row,rhs=item
        if not 0<=row<1<<(3*m) or rhs not in (0,1):
            raise ValueError("invalid raw affine row")
        return (sum(((row&v).bit_count()%2)<<j for j,v in enumerate(chart.cols)),
                rhs^((row&chart.base).bit_count()%2))
    pp=tuple(map(pull,pins))
    ne=None if inequality is None else tuple(map(pull,inequality))
    selected=[]
    rowspace={}
    for row,b in pp:
        if insert(row>>(2*m),0,rowspace):
            selected.append((row,b))
    if len(selected)!=m:
        return "UNKNOWN"
    # Solve the m slack pivots for z as an affine binary function of x,y.
    def section(w):
        s=affine_domain(m,((row>>(2*m),b^((row&w).bit_count()%2)) for row,b in selected))
        return w|(s[0]<<(2*m))
    z0,zc=raw_frame(lambda w:section(w)>>(2*m),2*m)
    A=linearized(f,zc[:m])
    B=linearized(f,zc[m:])
    # Inverse Frobenius on coefficients identifies the common null line of
    # all degree >=4 terms independently of the recovered K-plane basis.
    axis=next(((a,b,j) for j,(a,b) in enumerate(zip(A,B)) if j>=2 and (a or b)),None)
    if axis is None:
        return "UNKNOWN"
    a,b,j=axis
    for _ in range(m-j):
        a,b=f.mul(a,a),f.mul(b,b)
    v=(b,a)
    u=(1,0) if a else (0,1)
    def vector(t,s):
        return (f.mul(t,u[0])^f.mul(s,v[0]))|((f.mul(t,u[1])^f.mul(s,v[1]))<<m)
    def product_eq(t,s):
        w=vector(t,s)
        z=z0^apply_basis(zc,w)
        return f.mul(w&mask,w>>m)^z^coordinates(chart.output_basis)(target)
    # q(t,s)=g*t*s + L(t) + b*s + c. Verify on all weight <=2 points.
    c=product_eq(0,0)
    g=f.mul(u[0],v[1])^f.mul(u[1],v[0])
    bs=product_eq(0,1)^c
    L=linearized(f,[product_eq(1<<i,0)^c for i in range(m)])
    def l_at(t):
        return apply_basis([product_eq(1<<i,0)^c for i in range(m)],t)
    def predicted(w):
        t,s=w&mask,w>>m
        return f.mul(f.mul(g,t)^bs,s)^l_at(t)^c
    if interpolate(predicted,2*m)!=interpolate(lambda w:product_eq(w&mask,w>>m),2*m):
        return "UNKNOWN"
    # Normalize T=t+b/g. Then s=(L(T)+c')/(g*T) away from T=0.
    shift=f.mul(bs,f.inverse(g))
    c^=l_at(shift)
    def row_on_ts(item):
        row,b=item
        fn=lambda w:((row&section(vector((w&mask)^shift,w>>m))).bit_count()%2)
        offset,cols=raw_frame(fn,2*m)
        return sum(v<<i for i,v in enumerate(cols)),b^offset
    pc=tuple(map(row_on_ts,pp))
    nc=None if ne is None else tuple(map(row_on_ts,ne))
    if not c:
        exc=affine_domain(m,((row>>m,b) for row,b in pc))
        if exc is not None:
            val,basis,_=exc
            if nc is None or any(((r>>m)&val).bit_count()%2!=b or any(
                    ((r>>m)&v).bit_count()%2 for v in basis) for r,b in nc):
                return "SAT"
    # Normalize the remaining binary checks before their product expansion.
    echelon={}
    for row,b in pc:
        rem,delta=reduce_vector(row,echelon)
        if rem:
            echelon[rem.bit_length()-1]=(rem,b^delta)
        elif b^delta:
            return "UNSAT"
    trace_basis={}
    for i in range(m):
        insert(f.trace_row(1<<i),1<<i,trace_basis)
    def toggle(p,e,a):
        e%=mask
        value=p.get(e,0)^a
        if value:
            p[e]=value
        else:
            p.pop(e,None)
    def bit_poly(row,constant):
        a=reduce_vector(row&mask,trace_basis)[1]
        b=reduce_vector(row>>m,trace_basis)[1]
        p={}
        toggle(p,1,a)
        b=f.mul(b,f.inverse(g))
        toggle(p,-1,f.mul(b,c))
        for j,z in enumerate(L):
            toggle(p,(1<<j)-1,f.mul(b,z))
        result={0:1} if constant else {}
        for _ in range(m):
            for e,vv in p.items():
                toggle(result,e,vv)
            p={(2*e)%mask:f.mul(vv,vv) for e,vv in p.items()}
        return result
    def multiply(x,y):
        z={}
        for i,aa in x.items():
            for j,bb in y.items():
                toggle(z,i+j,f.mul(aa,bb))
        return z
    product={0:1}
    for row,b in echelon.values():
        product=multiply(product,bit_poly(row,1^b))
        if not product:
            return "UNSAT"
        if max_terms is not None and len(product)>max_terms:
            return "UNKNOWN"
    if nc is None:
        return "SAT"
    for row,b in nc:
        test=multiply(product,bit_poly(row,b))
        if test:
            if max_terms is not None and len(test)>max_terms:
                return "UNKNOWN"
            return "SAT"
    return "UNSAT"


def self_test():
    from random import Random
    from punctured_witness import BinaryField
    from double_polar_chart import recover
    rng=Random(491)
    def random_basis(d):
        basis=()
        while len(basis)<d:
            basis=independent((*basis,rng.randrange(1,1<<d)))
        return basis
    for m,mod in [(3,11),(5,37)]:
        n=3*m
        f=BinaryField(mod)
        ib,ob=random_basis(n),random_basis(m)
        off,oc=rng.randrange(1<<n),rng.randrange(1<<m)
        def xyz(x):
            return chunks(apply_basis(ib,x^off),m,3)
        def raw(x):
            a,b,z=xyz(x)
            return apply_basis(ob,f.mul(a,b)^z)^oc
        def restriction(x):
            a,b,z=xyz(x)
            return z^f.mul(f.mul(a,a),f.mul(a,a))
        c,cols=raw_frame(restriction,n)
        pins=[(sum(((col>>i)&1)<<j for j,col in enumerate(cols)),(c>>i)&1) for i in range(m)]
        data=interpolate(raw,n)
        chart=prepare(n,m,*data)
        assert chart is not None
        start,basis,_=affine_domain(n,pins)
        compare=lambda x:raw(start^apply_basis(basis,x))
        assert recover(2*m,m,*interpolate(compare,2*m)) is None
        domain=[start^apply_basis(basis,i) for i in range(1<<(2*m))]
        for i in range(14):
            extra=[(rng.randrange(1<<n),rng.randrange(2)) for j in range(i%4)]
            ne=[(rng.randrange(1<<n),rng.randrange(2)) for j in range(i%3)] if i%2 else None
            t=rng.randrange(1<<m)
            truth=any(raw(x)==t and all((x&r).bit_count()%2==b for r,b in extra)
                      and (ne is None or any((x&r).bit_count()%2!=b for r,b in ne)) for x in domain)
            ans=decide(chart,t,(*pins,*extra),ne)
            assert ans==("SAT" if truth else "UNSAT"),(m,i,ans,truth)
        assert decide(chart,0,[])=="UNKNOWN"
        print(f"GF(2^{m}) recoded product, quartic slack and 14 exhaustive side conditions passed")


if __name__=="__main__":
    self_test()
