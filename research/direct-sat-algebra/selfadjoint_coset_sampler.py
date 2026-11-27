"""Safe shift on a quadratic-subfield line for self-adjoint binary columns."""
from additive_safe_slope import _safe
from quadratic_target import affine_domain


def subfield_basis(field):
    columns=[]
    for i in range(field.m):
        x=1<<i
        for _ in range(field.m//2):
            x=field.mul(x,x)
        columns.append(x^(1<<i))
    rows=[sum(((v>>j)&1)<<i for i,v in enumerate(columns)) for j in range(field.m)]
    _,basis,_=affine_domain(field.m,[(r,0) for r in rows])
    return basis


def _center(field,cols):
    m=field.m
    if len(cols)!=m or any(not 0<=v<field.size for v in cols):
        raise ValueError("invalid binary columns")
    # Compute the scalar removing the diagonal of Tr(x A(y)).
    pairing=[field.trace_row(v) for v in cols]
    if any((pairing[i]>>j ^ pairing[j]>>i)&1 for i in range(m) for j in range(i)):
        raise ValueError("not trace-self-adjoint")
    equations=[(field.trace_row(field.mul(1<<i,1<<i)),pairing[i]>>i&1) for i in range(m)]
    center,kernel,_=affine_domain(m,equations)
    if kernel:
        raise ArithmeticError("degenerate square trace pairing")
    return center


def find(field,cols,scale=1):
    """Original columns; scan a centered half-field line or inverse-cube sampler."""
    m=field.m
    if not 0<scale<field.size or not (m%4==2 or (m>=5 and m%2)):
        raise ValueError("requires degree 2 mod 4 or odd degree at least 5")
    center=_center(field,cols)
    if m%2:
        # y ranges over a fixed codimension-two additive space; z^(-3)=y.
        exponent=pow(-3,-1,field.size-1)
        for y in range(1,1<<(m-2)):
            z=1
            base=y
            k=exponent
            while k:
                if k&1:
                    z=field.mul(z,base)
                base=field.mul(base,base)
                k>>=1
            s=center^field.mul(scale,z)
            if _safe(field,cols,s):
                return s
        raise ArithmeticError("odd inverse-cube fiber had no witness")
    if _safe(field,cols,center):
        return center
    basis=[field.mul(scale,v) for v in subfield_basis(field)]
    s=center
    for k in range(1,1<<len(basis)):
        s^=basis[(k&-k).bit_length()-1]
        if _safe(field,cols,s):
            return s
    raise ArithmeticError("odd sampled fiber had no witness")


if __name__=="__main__":
    from random import Random
    from punctured_witness import BinaryField
    from additive_safe_slope import _columns
    rng=Random(71)
    for mod in (7,67,1033):
        f=BinaryField(mod)
        h=f.m//2
        sub=[0]
        for v in subfield_basis(f):
            sub.extend([x^v for x in sub])
        for trial in range(12):
            a=[0]*f.m
            a[0]=rng.randrange(f.size)
            for j in range(1,h):
                v=rng.randrange(f.size)
                a[j]=v
                for _ in range(f.m-j):
                    v=f.mul(v,v)
                a[f.m-j]=v
            a[h]=rng.choice(sub)
            cols=_columns(f,a)
            for scale in (1,rng.randrange(1,f.size)):
                answer=find(f,cols,scale)
                tested={a[0]^f.mul(scale,x) for x in sub}
                assert answer in tested and _safe(f,cols,answer)
                assert sum(_safe(f,cols,x) for x in tested)%2==1
    print("72 centered line parities and returned ranks verified in degrees 2,6,10")

    for mod in (37,131,529):
        f=BinaryField(mod)
        for _ in range(5):
            a=[rng.randrange(f.size)]+[0]*(f.m-1)
            for j in range(1,(f.m+1)//2):
                v=rng.randrange(f.size)
                a[j]=v
                for _ in range(f.m-j):
                    v=f.mul(v,v)
                a[f.m-j]=v
            cols=_columns(f,a)
            scale=rng.randrange(1,f.size)
            safe=find(f,cols,scale)
            members=[]
            for z in range(1,f.size):
                inv=f.inverse(f.mul(z,f.mul(z,z)))
                if inv<(1<<(f.m-2)):
                    members.append(a[0]^f.mul(scale,z))
            assert safe in members and _safe(f,cols,safe)
            assert sum(_safe(f,cols,s) for s in members)%2==1
    print("15 full inverse-cube sampler parities checked in degrees 5,7,9")
