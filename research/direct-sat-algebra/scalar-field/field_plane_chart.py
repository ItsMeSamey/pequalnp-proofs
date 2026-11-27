"""Verify a supplied binary input chart for two field variables and count joint targets.

fit(field, output_count, constant, linear, pairs, input_basis, input_offset, k)
takes a packed raw ANF on 2m bits with output_count chunks of m bits and
an invertible field-coordinate-to-raw input chart. Each output is fitted to
one constant and degree-one/two products of Frobenius layers [-k,k]. Changing
both field coordinates by the same Frobenius gives ordinary low exponents.
A successful Chart counts arbitrary packed raw targets with raw binary pins.
Witness extraction uses deterministic exceptional fibers and Las Vegas smooth
fibers; a preceding exact count on the same compiled polynomial is reused.
"""
from dataclasses import dataclass, field as data_field
from itertools import combinations, combinations_with_replacement
from field_plane_targets import _eval, _reduce_degree, compile_plane, count
from field_rank_drift import field_solve
from quadratic_image import parity
from quadratic_target import apply_basis, evaluate_anf, insert, interpolate, reduce_vector


def _frob(field,x,k):
    for _ in range(k % field.m):
        x=field.mul(x,x)
    return x


@dataclass
class Chart:
    field: object
    outputs: tuple
    basis: tuple
    offset: int
    anf: tuple
    _last_count: tuple = data_field(default=None,init=False,repr=False,compare=False)

    def raw(self,u,v):
        return self.offset ^ apply_basis(self.basis,u|(v<<self.field.m))

    def _constraints(self,target,pins):
        f=self.field
        if type(target) is not int or not 0<=target<1<<(f.m*len(self.outputs)):
            raise ValueError("invalid packed output target")
        targets=tuple((target>>(j*f.m))&(f.size-1) for j in range(len(self.outputs)))
        transformed=[]
        for row,c in pins:
            if not 0<=row<1<<(2*f.m) or c not in (0,1):
                raise ValueError("invalid raw pin")
            transformed.append((sum(parity(row&x)<<i for i,x in enumerate(self.basis)),
                                c^parity(row&self.offset)))
        return targets,transformed

    def count(self,target,pins=(),*,point_count=None):
        targets,transformed=self._constraints(target,pins)
        if self.field.size<=8 and point_count is None:
            return count(self.field,self.outputs,targets,transformed)
        if point_count is None:
            from torus_carry_count import point_count
        recorded=[]
        def capture(f,poly):
            value=point_count(f,poly)
            recorded.append((tuple(sorted(poly.items())),value))
            return value
        result=count(self.field,self.outputs,targets,transformed,point_count=capture)
        if recorded:
            self._last_count=recorded[0]
        return result

    def witness(self,target,pins=(),*,point_count=None,rng=None):
        """Return a checked raw witness or None; reuse a matching exact count."""
        from field_plane_root import root
        pins=tuple(pins)
        targets,transformed=self._constraints(target,pins)
        cert=compile_plane(self.field,self.outputs,targets,transformed)
        if cert is None:
            return None
        cached=self._last_count
        if cached is not None and cached[0]==tuple(sorted(cert.polynomial.items())):
            if not cached[1]:
                return None
            point_count=lambda f,p:cached[1]
        parameter=root(self.field,cert.polynomial,point_count=point_count,rng=rng)
        if parameter is None:
            return None
        u,v=(_eval(self.field,p,*parameter) for p in (cert.x,cert.y))
        x=self.raw(u,v)
        if evaluate_anf(*self.anf,x)!=target or any(parity(row&x)!=c for row,c in pins):
            raise ArithmeticError("field chart witness fails raw tuple or raw pins")
        return x


def fit(field, output_count, constant, linear, pairs, input_basis, input_offset=0, k=0):
    f=field
    m,n=f.m,2*f.m
    linear,input_basis=tuple(linear),tuple(input_basis)
    if type(k) is not int or k<0 or output_count<0 or len(linear)!=n or len(input_basis)!=n:
        raise ValueError("invalid field-plane chart dimensions")
    if any(not 0<=a<1<<n for a in (*input_basis,input_offset)):
        raise ValueError("invalid supplied input chart")
    if (any(not 0<=a<1<<(m*output_count) for a in (constant,*linear,*pairs.values())) or
            any(not 0<=i<j<n for i,j in pairs)):
        raise ValueError("invalid raw ANF")
    # Old variable = new variable^(2^k); old layer j becomes new layer j+k.
    basis=tuple(apply_basis(input_basis,_frob(f,1<<i,k)<<(j*m))
                for j in range(2) for i in range(m))
    rows={}
    for i,b in enumerate(basis):
        if not insert(b,1<<i,rows):
            raise ValueError("singular supplied binary input chart")
    atoms=[(1<<i,0) for i in range(min(m,2*k+1))]+[(0,1<<i) for i in range(min(m,2*k+1))]
    monomials={(0,0),*atoms}
    for (a,b),(c,d) in combinations_with_replacement(atoms,2):
        monomials.add((_reduce_degree(a+c,f.size),_reduce_degree(b+d,f.size)))
    monomials=sorted(monomials)
    samples=[0]+[1<<i for i in range(n)]+[(1<<i)|(1<<j) for i,j in combinations(range(n),2)]
    anf=(constant,linear,{e:v for e,v in pairs.items() if v})
    functions=[]
    values=[]
    for x in samples:
        _,z=reduce_vector(x^input_offset,rows)
        u,v=z&(f.size-1),z>>m
        functions.append([_eval(f,{e:1},u,v) for e in monomials])
        values.append(evaluate_anf(*anf,x))
    outputs=[]
    for j in range(output_count):
        solution=field_solve(f,((r,(v>>(j*m))&(f.size-1)) for r,v in zip(functions,values)),
                             len(monomials))
        if solution is None:
            return None
        outputs.append({e:c for e,c in zip(monomials,solution) if c})
    def raw_value(x):
        _,z=reduce_vector(x^input_offset,rows)
        u,v=z&(f.size-1),z>>m
        return sum(_eval(f,p,u,v)<<(i*m) for i,p in enumerate(outputs))
    # Every fitted monomial is a product of at most two binary-linear functions
    # before the affine chart. Thus weight <=2 recovers the *full* raw ANF.
    if interpolate(raw_value,n)!=(constant,list(linear),anf[2]):
        raise ArithmeticError("fitted polynomial identity fails raw coefficient verification")
    return Chart(f,tuple(outputs),basis,input_offset,anf)


def check():
    from punctured_witness import BinaryField
    from quadratic_centroid import independent
    from random import Random
    from unittest.mock import patch
    import torus_carry_count
    rng=Random(7821)
    def fixture(mod,k,body,width):
        f=BinaryField(mod)
        n=2*f.m
        cols=()
        while len(cols)<n:
            cols=independent((*cols,rng.randrange(1<<n)))
        shift=rng.randrange(1,1<<n)
        rows={}
        for i,c in enumerate(cols):
            insert(c,1<<i,rows)
        def raw(x):
            _,z=reduce_vector(x^shift,rows)
            return body(f,z&(f.size-1),z>>f.m)
        chart=fit(f,width,*interpolate(raw,n),cols,shift,k)
        assert chart is not None
        return chart,raw
    def low(f,u,v):
        x=f.mul(u,u)^f.mul(u,v)
        return x|((x^1)<<f.m)
    chart,raw=fixture(19,0,low,2)
    target=1<<4
    truth=sum(raw(x)==target for x in range(256))
    with patch.object(torus_carry_count,"point_count",wraps=torus_carry_count.point_count) as native:
        got=chart.count(target)
        assert native.call_count==1
    assert got==truth==31 and raw(chart.witness(target))==target
    pins=((7,0),(37,1))
    w=chart.witness(target,pins)
    assert raw(w)==target and all(parity(v&w)==c for v,c in pins)
    assert chart.witness(0) is None
    # Independent output coordinates, with a real pin included in the native
    # call. uv=u=0 forces u=0; the independent v-bit leaves eight points.
    joint, original=fixture(19,0,lambda f,u,v:f.mul(u,v)|(u<<f.m),2)
    dual={}
    for i,col in enumerate(joint.basis):
        insert(col,1<<i,dual)
    row=sum(((reduce_vector(1<<j,dual)[1]>>4)&1)<<j for j in range(8))
    pins=((row,1^parity(row&joint.offset)),)
    with patch.object(torus_carry_count,"point_count",wraps=torus_carry_count.point_count) as native:
        assert joint.count(0,pins)==8 and native.call_count==1
    x=joint.witness(0,pins)
    assert original(x)==0 and parity(row&x)==pins[0][1]
    # Negative and positive old layers occur in one product.
    def shifted(f,u,v):
        return f.mul(_frob(f,u,-1),_frob(f,v,1))^_frob(f,v,-1)^2
    tiny,raw2=fixture(11,1,shifted,1)
    for t in range(8):
        for pins in ((),((13,1),),((9,0),(9,1))):
            truth=sum(raw2(x)==t and all(parity(mask&x)==b for mask,b in pins)
                      for x in range(64))
            assert tiny.count(t,pins)==truth
            w=tiny.witness(t,pins)
            assert (w is not None)==bool(truth)
            if w is not None:
                assert raw2(w)==t
    f=BinaryField(19)
    assert fit(f,1,*interpolate(lambda x:_frob(f,x&15,2),8),
               tuple(1<<j for j in range(8)),0,0) is None
    # Force the first 2D random fibers to miss a smooth GF512 parabola.
    # The count of a translated parabola is q, and the cached count avoids
    # a second call before the third trial yields a rational point.
    large,large_raw=fixture(529,0,lambda f,u,v:f.mul(v,v)^u^v,1)
    target=0
    class Trials:
        def __init__(self):
            self.trials=iter([1,1,1,1,0])
        def randrange(self,_):
            return next(self.trials)
    calls=[]
    def parabola_count(f,poly):
        calls.append(1)
        return f.size
    assert large.count(target,point_count=parabola_count)==512
    with patch.object(torus_carry_count,"point_count",side_effect=AssertionError("duplicate count")):
        assert large_raw(large.witness(target,rng=Trials()))==target
    assert calls==[1]
    print("GF16 dense-chart native counts 31 and 8, raw lifts and 24 signed-layer pin comparisons passed")


if __name__=="__main__":
    check()
