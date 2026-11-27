"""Find a rational affine plane point over a supplied binary field.

root(field,P) returns (x,y) or None. Coefficients are field elements and
keys are nonnegative exponent pairs. Expected bit complexity is polynomial
in the numerical total degree and field degree. Singular/exceptional fibers
are tested deterministically; remaining nonempty curves use Las Vegas search.
The optional point_count(field,P) supplies exact affine counts. By default
the native torus-carry counter is used if an emptiness check is needed.
"""
from random import SystemRandom


def trim(v):
    v=list(v)
    while v and not v[-1]:
        v.pop()
    return tuple(v)


def add(a,b):
    return trim([(a[i] if i<len(a) else 0)^(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))])


def scale(f,a,c):
    return trim(f.mul(x,c) for x in a)


def mul(f,a,b):
    out=[0]*(len(a)+len(b))
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]^=f.mul(x,y)
    return trim(out)


def divmod1(f,a,b):
    if not b:
        raise ZeroDivisionError
    q=[0]*max(0,len(a)-len(b)+1)
    inv=f.inverse(b[-1])
    while a and len(a)>=len(b):
        k=len(a)-len(b)
        t=f.mul(a[-1],inv)
        q[k]=t
        a=add(a,(0,)*k+scale(f,b,t))
    return trim(q),a


def exact(f,a,b):
    q,r=divmod1(f,a,b)
    if r:
        raise ArithmeticError("inexact polynomial division")
    return q


def gcd1(f,a,b):
    while b:
        a,b=b,divmod1(f,a,b)[1]
    return scale(f,a,f.inverse(a[-1])) if a else ()


def ev(f,a,x):
    y=0
    for c in reversed(a):
        y=f.mul(y,x)^c
    return y


def rational_roots(f,a):
    """All roots of a nonzero univariate polynomial, without scanning K."""
    if not a:
        raise ValueError("identically zero polynomial")
    if len(a)==1:
        return []
    x=(0,1)
    p=x
    for _ in range(f.m):
        p=divmod1(f,mul(f,p,p),a)[1]
    g=gcd1(f,a,add(p,x))
    if len(g)==1:
        return []
    factors=[g]
    for j in range(f.m):
        if all(len(h)==2 for h in factors):
            break
        p=(0,1<<j)
        trace=()
        for _ in range(f.m):
            trace=add(trace,p)
            p=divmod1(f,mul(f,p,p),g)[1]
        split=[]
        for h in factors:
            part=gcd1(f,h,trace)
            split.extend(t for t in (part,exact(f,h,part)) if len(t)>1)
        factors=split
    if any(len(h)!=2 for h in factors):
        raise ArithmeticError("trace splitting failed")
    return [f.mul(h[0],f.inverse(h[1])) for h in factors]


# Bivariate polynomials are tuples of Y-coefficients, each an X-polynomial.
def content(f,a):
    g=()
    for c in a:
        g=gcd1(f,g,c)
    return g


def primitive(f,a):
    if not a:
        return ()
    c=content(f,a)
    return tuple(exact(f,t,c) for t in a)


def plus(a,b):
    return trim(add(a[i] if i<len(a) else (),b[i] if i<len(b) else ())
                for i in range(max(len(a),len(b))))


def times(f,a,b):
    out=[()]*(len(a)+len(b))
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]=add(out[i+j],mul(f,x,y))
    return trim(out)


def primitive_remainder(f,a,b):
    # Divide over K(X), clearing denominators and removing content at each
    # cancellation; primitive Euclidean remainders are subresultants up to units.
    while a and len(a)>=len(b):
        k=len(a)-len(b)
        t=a[-1]
        a=primitive(f,plus(tuple(mul(f,c,b[-1]) for c in a),
                           ((),)*k+tuple(mul(f,c,t) for c in b)))
    return a


def gcd2(f,a,b):
    c=gcd1(f,content(f,a),content(f,b))
    a,b=primitive(f,a),primitive(f,b)
    while b:
        a,b=b,primitive_remainder(f,a,b)
    if not a:
        return ()
    inv=f.inverse(a[-1][-1])
    return tuple(scale(f,mul(f,c,t),inv) for t in a)


def quotient(f,a,b):
    q=[()]*(max(0,len(a)-len(b)+1))
    while a and len(a)>=len(b):
        k=len(a)-len(b)
        q[k]=exact(f,a[-1],b[-1])
        a=plus(a,((),)*k+tuple(mul(f,t,q[k]) for t in b))
    if a:
        raise ArithmeticError("inexact bivariate quotient")
    return trim(q)


def derivatives(a):
    dx=trim(trim(t[i] if i%2 else 0 for i in range(1,len(t))) for t in a)
    dy=trim(a[i] if i%2 else () for i in range(1,len(a)))
    return dx,dy


def radical(f,a):
    if len(a)==1 and len(a[0])==1:
        return ((1,),)
    dx,dy=derivatives(a)
    h=gcd2(f,gcd2(f,a,dx),dy)
    odd=quotient(f,a,h)
    if len(h)==1 and len(h[0])==1:
        return odd
    square=trim(trim(f.sqrt(c) for c in t[::2]) for t in h[::2])
    rr=radical(f,square)
    return times(f,odd,quotient(f,rr,gcd2(f,odd,rr)))


def power(f,a,k):
    result=1
    while k:
        if k&1:
            result=f.mul(result,a)
        a=f.mul(a,a)
        k//=2
    return result


def resultant_value(f,a,b):
    result=1
    while len(b)>1:
        if not a:
            return 0
        if len(a)<len(b):
            a,b=b,a
            continue
        r=divmod1(f,a,b)[1]
        if not r:
            return 0
        result=f.mul(result,power(f,b[-1],len(a)-len(r)))
        a,b=b,r
    return f.mul(result,power(f,b[0],len(a)-1)) if b else 0


def specialize(f,a,x):
    return trim(ev(f,c,x) for c in a)


def resultant(f,a,b):
    # Interpolate the Sylvester determinant from specializations preserving
    # both Y degrees. The large-field branch has enough admissible x.
    bound=(len(a)-1)*max(len(c)-1 for c in b)+(len(b)-1)*max(len(c)-1 for c in a)
    interp=()
    product=(1,)
    used=0
    for x in range(f.size):
        aa,bb=specialize(f,a,x),specialize(f,b,x)
        if len(aa)!=len(a) or len(bb)!=len(b):
            continue
        value=resultant_value(f,aa,bb)^ev(f,interp,x)
        interp=add(interp,scale(f,product,f.mul(value,f.inverse(ev(f,product,x)))))
        product=mul(f,product,(x,1))
        used+=1
        if used==bound+1:
            return interp
    raise ArithmeticError("insufficient field for resultant interpolation")


def root(field,polynomial,*,point_count=None,rng=None):
    f=field
    if any(type(i) is not int or type(j) is not int or min(i,j)<0
           or type(v) is not int or not 0<=v<f.size for (i,j),v in polynomial.items()):
        raise ValueError("invalid plane polynomial")
    poly={e:v for e,v in polynomial.items() if v}
    if not poly:
        return 0,0
    D=max(i+j for i,j in poly)
    if D==0:
        return None
    a=trim(trim(poly.get((i,j),0) for i in range(D-j+1)) for j in range(D+1))
    def on_fiber(F,x):
        fiber=specialize(f,F,x)
        if not fiber:
            return x,0
        ys=rational_roots(f,fiber)
        return (x,ys[0]) if ys else None
    if f.size<16*D**4:
        for x in range(f.size):
            answer=on_fiber(a,x)
            if answer is not None:
                return answer
        return None
    F=radical(f,a)
    c=content(f,F)
    roots=rational_roots(f,c)
    if roots:
        return roots[0],0
    F=primitive(f,F)
    if len(F)==1:
        return None
    dx,dy=derivatives(F)
    for s in range(D+1):
        g=plus(dx,tuple(scale(f,t,s) for t in dy))
        if g and gcd2(f,F,g)==((1,),):
            break
    else:
        raise ArithmeticError("squarefree derivative separation failed")
    res=resultant(f,F,g)
    if not res:
        raise ArithmeticError("resultant unexpectedly vanished")
    for x in rational_roots(f,res):
        answer=on_fiber(F,x)
        if answer is not None:
            return answer
    # Only smooth points remain. If any exist, a random fiber succeeds with
    # probability at least 1/(2D). Bound initial trials before exact emptiness.
    generator=SystemRandom() if rng is None else rng
    for _ in range(2*D):
        answer=on_fiber(F,generator.randrange(f.size))
        if answer is not None:
            return answer
    if point_count is None:
        from torus_carry_count import point_count
    if not point_count(f,poly):
        return None
    while True:
        answer=on_fiber(F,generator.randrange(f.size))
        if answer is not None:
            return answer


def self_test():
    from random import Random
    from punctured_witness import BinaryField
    from field_plane_targets import _eval
    rng=Random(164)
    small=BinaryField(7)
    for _ in range(45):
        p={(i,j):rng.randrange(4) for i in range(4) for j in range(4-i)}
        found=root(small,p,rng=rng)
        brute=[(x,y) for x in range(4) for y in range(4) if _eval(small,p,x,y)==0]
        assert found in brute if brute else found is None
    f=BinaryField(529)
    k=next(i for i in range(f.size) if f.trace(i))
    class NoSampling:
        def randrange(self,*_):
            raise AssertionError("singular witness did not take deterministic path")
    # Conjugate lines have a unique rational point, far from the origin.
    x0,y0=27,39
    p={(2,0):1,(1,1):1,(0,2):k,(1,0):y0,(0,1):x0,
       (0,0):f.mul(x0,x0)^f.mul(x0,y0)^f.mul(k,f.mul(y0,y0))}
    assert root(f,p,rng=NoSampling())==(x0,y0)
    assert root(f,{(2,0):1,(0,0):f.mul(x0,x0)},rng=NoSampling())==(x0,0)
    # Directly exercise repeated, mixed, and purely inseparable radicals.
    a=((0,1),(1,))  # X+Y
    b=((1,),(1,))   # 1+Y
    rep=times(f,times(f,a,a),times(f,times(f,b,b),b))
    assert radical(f,rep)==times(f,a,b)
    smooth={(0,1):1,(2,0):1,(0,0):47}
    ans=root(f,smooth,rng=rng)
    assert _eval(f,smooth,*ans)==0
    empty={(2,0):1,(0,2):1,(1,0):1,(0,1):1,(0,0):k}
    calls=[]
    def empty_count(field,poly):
        calls.append(1)
        assert poly==empty and field.trace(k)
        return 0
    assert root(f,empty,rng=rng,point_count=empty_count) is None and calls==[1]
    print("45 tiny curves and repeated, inseparable, conjugate, vertical, empty and smooth controls passed")


if __name__=='__main__':
    self_test()
