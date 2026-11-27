"""Decision and exact counting for a raw binary vector quadratic target.

Use problem = Target(n,m,c,linear,pairs), then problem.decide(t) or
problem.count(t,point_count=...). Decision returns (exists, witness_or_None);
a Hasse-bound certificate of existence need not produce an input.

For arbitrary ANFs the binary Fourier fallback uses 2^m polynomial-cost
Gauss sums (a polynomial number of repetitions for a witness). A certified
chart with h recovered pins also supports counting using 2^h polynomial
operations and at most 2^h curve-count calls. point_count(field,D) must count
projective points of y^2+xy=x^3+D^2 exactly. A chart is selected when h<m;
otherwise the direct character sum is used. The default curve backend scans
at most 63 nonzero coordinates on tiny fields, then switches to polynomial
Laurent carries. On a promised hidden slice both decision and exact counting
take 2^O(h) times polynomial bit work.
"""
from itertools import combinations
from double_polar_chart import recover
from quadratic_image import gauss,parity
from quadratic_target import affine_domain,apply_basis,evaluate_anf,insert,reduce_vector


def zero_plane(form,pins):
    """Intersect the zero cone of a nonsingular binary field plane with pins."""
    if all(b==0 for _,b in pins):
        return 0
    f=form.field
    a,c=form.squares
    b=form.cross[0,1]
    # Finite slopes (s,1) satisfy a*s^2+b*s=c, an affine binary system.
    rows={}
    for i in range(f.m):
        u=1<<i
        insert(f.mul(a,f.mul(u,u))^f.mul(b,u),u,rows)
    rem,slope=reduce_vector(c,rows)
    lines=[]
    if not rem:
        lines.append(slope | (1<<f.m))
        if a:  # b/a spans the binary kernel when the quadratic term is present.
            lines.append((slope^f.mul(b,f.inverse(a))) | (1<<f.m))
    if not a:
        lines.append(1)  # infinite slope
    for direction in lines:
        basis=[form.scale(1<<i,direction) for i in range(f.m)]
        restrictions=[(sum(parity(row&v)<<j for j,v in enumerate(basis)),rhs)
                      for row,rhs in pins]
        sol=affine_domain(f.m,restrictions)
        if sol is not None:
            return apply_basis(basis,sol[0])
    return None


class Target:
    def __init__(self,n,m,constant,linear,pairs):
        self.n,self.m=n,m
        self.anf=constant,tuple(linear),dict(pairs)
        self.chart=recover(n,m,*self.anf)

    def _check(self,t):
        if not 0<=t<1<<self.m:
            raise ValueError("target out of range")

    def _fourier(self,t,fixed=0,x=0):
        c,l,p=self.anf
        total=0
        for a in range(1<<self.m):
            f=(parity(a&(c^t)),sum(parity(a&v)<<i for i,v in enumerate(l)),
               frozenset(e for e,v in p.items() if parity(a&v)))
            total+=gauss(self.n,f,fixed,x)
        result,rem=divmod(total,1<<self.m)
        if rem or result<0:
            raise ArithmeticError("invalid Fourier fiber count")
        return result

    def count(self,t,*,point_count=None):
        self._check(t)
        if self.chart is not None and len(self.chart.normals)<self.m:
            form,goal,pins,_=self.chart.homogeneous(t)
            return form.count(goal,pins,point_count=point_count)
        return self._fourier(t)

    def decide(self,t):
        self._check(t)
        chart=self.chart
        if chart is not None and self.m>6*len(chart.normals):
            form,goal,pins,shift=chart.homogeneous(t)
            if form.d>2*len(pins):
                y=form.plane_witness(goal,pins)
                if y is None:
                    raise ArithmeticError("guaranteed field plane was not found")
            elif form.d==2 and not goal:
                y=zero_plane(form,pins)
                if y is None:
                    return False,None
            else:
                # For d>=4 the nonsingular Gauss bound gives positive mass.
                # For d=2 and goal!=0 use the binary Kloosterman/Hasse bound.
                return True,None
            x=chart.lift(y^shift)
        else:
            if not self._fourier(t):
                return False,None
            fixed=x=0
            for i in range(self.n):
                fixed|=1<<i
                if not self._fourier(t,fixed,x):
                    x|=1<<i
        if evaluate_anf(*self.anf,x)!=t:
            raise ArithmeticError("target witness failed original ANF")
        return True,x


def self_test():
    from random import Random
    from quadratic_target import interpolate
    from punctured_witness import BinaryField
    from scalar_field_pins import small_field_point_count
    rng=Random(952)
    checks=0
    for _ in range(32):
        n,m=rng.randrange(6),rng.randrange(4)
        data=(rng.randrange(1<<m),[rng.randrange(1<<m) for _ in range(n)],
              {e:rng.randrange(1<<m) for e in combinations(range(n),2)})
        problem=Target(n,m,*data)
        vals=[evaluate_anf(*data,x) for x in range(1<<n)]
        for t in range(1<<m):
            assert problem.count(t)==problem.count(t,point_count=small_field_point_count)==vals.count(t)
            sat,w=problem.decide(t)
            assert sat==(t in vals) and (w is None or vals[w]==t)
            checks+=1
    # A hidden affine pin excludes the origin. An anisotropic plane has no
    # zero; a split plane has an intersection with an isotropic line.
    f=BinaryField(131)
    m=7
    tr_one=next(x for x in range(1<<m) if f.trace(x))
    for d,diagonal in ((2,tr_one),(2,0),(4,0)):
        n=m*d-1
        normal=(1<<(m+1))^1
        offset,basis,_=affine_domain(n+1,[(normal,1)])
        def hidden(x):
            z=offset^apply_basis(basis,x)
            coords=[(z>>(i*m))&127 for i in range(d)]
            a,b=coords[:2]
            value=f.mul(a,b)^f.mul(a,a)^f.mul(diagonal,f.mul(b,b))
            return value if d==2 else value^f.mul(*coords[2:])
        problem=Target(n,m,*interpolate(hidden,n))
        assert problem.chart is not None and len(problem.chart.normals)==1
        for t in (0,1,93):
            answer,w=problem.decide(t)
            assert answer != (d==2 and diagonal!=0 and t==0)
            assert w is None or hidden(w)==t
            assert (problem.count(t,point_count=small_field_point_count)>0)==answer
            if d==2:
                expect=sum(hidden(x)==t for x in range(1<<n))
                assert problem.count(t)==expect
                assert problem.count(t,point_count=small_field_point_count)==expect
    # Verify the native default through a densely recoded raw chart. The
    # spy calls the actual carry routine, while the public call has no override.
    from unittest.mock import patch
    import laurent_carry
    d=2
    diagonal=tr_one
    def dense(x):
        v=x^(x>>1)^(x>>3)^(x>>5)
        z=offset2^apply_basis(basis2,v^412)
        a,b=z&127,z>>7
        y=f.mul(a,b)^f.mul(a,a)^f.mul(diagonal,f.mul(b,b))
        return y^(y>>1)^(y>>3)^47
    offset2,basis2,_=affine_domain(14,[(1|(2<<7),1)])
    instance=Target(13,7,*interpolate(dense,13))
    assert instance.chart is not None
    goal=dense(0)
    with patch.object(laurent_carry,"point_count",wraps=laurent_carry.point_count) as native:
        observed=instance.count(goal)
        assert native.call_count>0
    assert observed==sum(dense(x)==goal for x in range(8192))
    # Frobenius squared is binary linear and leaves the bilinear polar intact.
    # Its degree-four coordinate cannot be fitted by field linear/square terms.
    from double_polar_chart import polar_field
    g=BinaryField(11)
    def incompatible(x):
        u,v=x&7,x>>3
        return g.mul(u,v)^g.mul(g.mul(u,u),g.mul(u,u))
    anf=interpolate(incompatible,6)
    assert polar_field(6,3,*anf) is not None
    drifted=Target(6,3,*anf)
    assert drifted.chart is None
    full=[incompatible(x) for x in range(64)]
    for t in range(8):
        assert drifted.count(t)==full.count(t)
        yes,w=drifted.decide(t)
        assert yes and incompatible(w)==t
    print(f"{checks} small targets plus anisotropic, split and four-dimensional charts passed")


if __name__=="__main__":
    self_test()
