"""Joint target counting for bivariate polynomials over a supplied binary field.

compile_plane(field, outputs, targets, pins=()) returns a Certificate or None
for inconsistent pins. Each input/output polynomial is {(i,j):field_value};
a pin is (binary_mask,rhs), applied to the packed input x | (y << field.m).
count(..., point_count=callback) returns the exact original fiber cardinality.
The callback receives (field, compiled_bivariate_polynomial). The default
enumerates only constant-size fields q<=8 and uses torus_carry_count otherwise.

Each pulled-back pin is Tr(a*x+b*y)=c. If a is nonzero, replace x by
(z^2+z+c*delta+b*y)/a with Tr(delta)=1; the analogous substitution for y
handles a=0. Every admitted point has exactly two preimages per independent
pin. Combine target residuals in a balanced tree by u^2+u*v+delta*v^2:
over this field it vanishes exactly at (u,v)=(0,0). For h independent
pins, t target residuals and input numerical total degree D, the composed
polynomial has degree at most max(1,D)*2^h*2^ceil(log2(max(1,t))).
Monomial exponents are optionally reduced as field polynomial functions
using x^q=x. All compilation and native count costs are polynomial in that
degree, field degree and input length, with only two polynomial variables.
"""
from dataclasses import dataclass
from itertools import product
from quadratic_image import parity
from quadratic_target import insert, reduce_vector


def _reduce_degree(d, q):
    return 0 if d==0 else 1+(d-1)%(q-1)


def _put(p, e, v):
    c=p.get(e,0)^v
    if c:
        p[e]=c
    else:
        p.pop(e,None)


def _sum(*polys):
    out={}
    for p in polys:
        for e,v in p.items():
            _put(out,e,v)
    return out


def _scale(f,p,a):
    return {e:f.mul(a,b) for e,b in p.items()} if a else {}


def _mul(f,p,r):
    out={}
    for (i,j),a in p.items():
        for (s,t),b in r.items():
            e=(_reduce_degree(i+s,f.size),_reduce_degree(j+t,f.size))
            _put(out,e,f.mul(a,b))
    return out


def _square(f,p):
    out={}
    for (i,j),a in p.items():
        e=(_reduce_degree(2*i,f.size),_reduce_degree(2*j,f.size))
        _put(out,e,f.mul(a,a))
    return out


def _power(f,p,k):
    out={(0,0):1}
    while k:
        if k&1:
            out=_mul(f,out,p)
        k >>= 1
        if k:
            p=_square(f,p)
    return out


def _compose(f,p,x,y):
    out={}
    xp={i:_power(f,x,i) for i,_ in p}
    yp={j:_power(f,y,j) for _,j in p}
    for (i,j),a in p.items():
        for e,b in _mul(f,xp[i],yp[j]).items():
            _put(out,e,f.mul(a,b))
    return out


def _eval(f,p,x,y):
    def pow_element(a,k):
        out=1
        while k:
            if k&1:
                out=f.mul(out,a)
            k >>= 1
            if k:
                a=f.mul(a,a)
        return out
    out=0
    for (i,j),a in p.items():
        out ^= f.mul(a,f.mul(pow_element(x,i),pow_element(y,j)))
    return out


@dataclass
class Certificate:
    x: dict  # maps two free field coordinates to an original point
    y: dict
    polynomial: dict  # zeros in the free field plane satisfy all original targets
    pin_rank: int


def compile_plane(field, outputs, targets, pins=()):
    f=field
    outputs,targets=tuple(outputs),tuple(targets)
    if len(outputs)!=len(targets) or any(not 0<=t<f.size for t in targets):
        raise ValueError("invalid joint target")
    polys=[]
    for poly,t in zip(outputs,targets):
        p={}
        for (i,j),a in poly.items():
            if type(i) is not int or type(j) is not int or min(i,j)<0 or not 0<=a<f.size:
                raise ValueError("invalid polynomial monomial")
            _put(p,(_reduce_degree(i,f.size),_reduce_degree(j,f.size)),a)
        _put(p,(0,0),t)
        polys.append(p)
    rows={}
    for row,rhs in pins:
        if not 0<=row<1<<(2*f.m) or rhs not in (0,1):
            raise ValueError("invalid binary pin")
        rem,c=reduce_vector(row,rows)
        if rem:
            rows[rem.bit_length()-1]=(rem,c^rhs)
        elif c^rhs:
            return None

    X={(1,0):1}
    Y={(0,1):1}
    x,y=X,Y
    trace_rows={}
    for j in range(f.m):
        insert(f.trace_row(1<<j),1<<j,trace_rows)
    delta=next(1<<j for j in range(f.m) if f.trace(1<<j))
    for row,rhs in rows.values():
        # The chart is affine-additive on the current coordinates. Read its
        # composed pin on the binary basis, including the affine offset.
        def pin(u,v):
            return parity(row&(_eval(f,x,u,v)|(_eval(f,y,u,v)<<f.m)))
        bit=pin(0,0)
        rx=sum((pin(1<<j,0)^bit)<<j for j in range(f.m))
        ry=sum((pin(0,1<<j)^bit)<<j for j in range(f.m))
        rem_a,a=reduce_vector(rx,trace_rows)
        rem_b,b=reduce_vector(ry,trace_rows)
        if rem_a or rem_b or not (a or b):
            raise ArithmeticError("independent pin lost on covering chart")
        offset={(0,0):delta} if bit^rhs else {}
        if a:
            xx=_scale(f,_sum(_square(f,X),X,offset,_scale(f,Y,b)),f.inverse(a))
            yy=Y
        else:
            xx=X
            yy=_scale(f,_sum(_square(f,Y),Y,offset),f.inverse(b))
        x,y=_compose(f,x,xx,yy),_compose(f,y,xx,yy)
    work=[_compose(f,p,x,y) for p in polys]
    while len(work)>1:
        nxt=[]
        for j in range(0,len(work)-1,2):
            u,v=work[j:j+2]
            nxt.append(_sum(_square(f,u),_mul(f,u,v),_scale(f,_square(f,v),delta)))
        if len(work)%2:
            nxt.append(work[-1])
        work=nxt
    return Certificate(x,y,work[0] if work else {},len(rows))


def count(field, outputs, targets, pins=(), *, point_count=None):
    cert=compile_plane(field,outputs,targets,pins)
    if cert is None:
        return 0
    if point_count is not None:
        total=point_count(field,cert.polynomial)
    elif field.size<=8:
        total=sum(not _eval(field,cert.polynomial,x,y)
                  for x,y in product(range(field.size),repeat=2))
    else:
        from torus_carry_count import point_count as native
        total=native(field,cert.polynomial)
    if type(total) is not int or not 0<=total<=field.size**2:
        raise ArithmeticError("invalid affine point count")
    result,rem=divmod(total,1<<cert.pin_rank)
    if rem:
        raise ArithmeticError("point count violates equal covering multiplicity")
    return result


def check():
    from collections import Counter
    from random import Random
    from punctured_witness import BinaryField
    from torus_carry_count import point_count
    rng=Random(801)
    controls=0
    for polynomial in (7,11):
        f=BinaryField(polynomial)
        points=list(product(range(f.size),repeat=2))
        for _ in range(20):
            pins=[(rng.randrange(f.size**2),rng.randrange(2)) for i in range(rng.randrange(2*f.m+1))]
            if pins:
                pins.append(pins[0])
            outputs=[{(rng.randrange(4),rng.randrange(3)):rng.randrange(f.size)
                      for j in range(3)} for i in range(rng.randrange(5))]
            witness=rng.choice(points)
            targets=[_eval(f,p,*witness) for p in outputs]
            cert=compile_plane(f,outputs,targets,pins)
            expected=Counter((x,y) for x,y in points
                             if all(parity(row&(x|(y<<f.m)))==rhs for row,rhs in pins))
            if cert is None:
                assert not expected
            else:
                actual=Counter((_eval(f,cert.x,x,y),_eval(f,cert.y,x,y)) for x,y in points)
                assert actual=={pt:1<<cert.pin_rank for pt in expected}
                for u,v in points:
                    x,y=_eval(f,cert.x,u,v),_eval(f,cert.y,u,v)
                    assert (_eval(f,cert.polynomial,u,v)==0)==all(_eval(f,p,x,y)==t for p,t in zip(outputs,targets))
            truth=sum(all(_eval(f,p,x,y)==t for p,t in zip(outputs,targets)) for x,y in expected)
            assert count(f,outputs,targets,pins)==truth
            controls+=1
    f=BinaryField(7)
    assert count(f,[{(1,0):1}],[1],[(4,1)],point_count=point_count)==2
    assert count(f,[{(1,0):1},{(0,1):1}],[1,2],[(1,1)],point_count=point_count)==1
    f=BinaryField(19)
    assert count(f,[{(1,0):1}],[0])==16
    print(f"{controls} exhaustive chart/multiplicity/target controls and three native counts passed")


if __name__=="__main__":
    check()
