"""Exact target counts with bounded signed Frobenius drift and binary pins.

count(form, drift, target, pins, constant=0, point_count=None) uses ScalarForm;
drift[(i,j)] multiplies x_i^(2^j), with signed j indexing Frobenius modulo m.
A supplied backend point_count(field,poly) returns the *affine* point count
of a sparse two-variable polynomial {(v_exp,y_exp): field coefficient}.
The default torus_carry_count backend has polynomial bit complexity in the
field degree and numerical polynomial degrees. sparse_point_count provides an
explicit exhaustive reference backend for small-field controls.
"""
from itertools import combinations, product
from quadratic_image import bits, gauss, parity
from quadratic_target import affine_domain, apply_basis, reduce_vector
from field_rank_drift import field_solve


def frob(f, x, j):
    for _ in range(j % f.m):
        x = f.mul(x,x)
    return x


def power(f, x, d):
    result = 1
    while d:
        if d & 1:
            result = f.mul(result,x)
        x = f.mul(x,x)
        d >>= 1
    return result


def sparse_point_count(f, poly):
    """Reference backend: enumerate affine v, solve linearized equation in y."""
    total = 0
    for x in range(f.size):
        coeffs = [0,0,0]
        for (i,j),a in poly.items():
            coeffs[j] ^= f.mul(a,power(f,x,i))
        c,b,a = coeffs
        if a != b:
            raise ValueError("reference backend expects Artin-Schreier form")
        if not a:
            total += f.size if not c else 0
        elif not f.trace(f.mul(c,f.inverse(a))):
            total += 2
    return total


def fit_affine(field, d, origin, basis, origin_value, differences, k):
    """Fit an additive drift plus constant on a supplied binary affine slice.

    differences are f(origin+w)^f(origin) on its basis. This presupposes
    the residual is affine there; additive samples alone do not certify degree.
    """
    if k < 0 or len(basis) != len(differences):
        raise ValueError("invalid exponent bound or data")
    labels = [(i,j) for i in range(d) for j in range(-k,k+1)]
    def row(x):
        return [frob(field,(x>>(i*field.m))&(field.size-1),j) for i,j in labels]
    solution = field_solve(field,((row(x),v) for x,v in zip(basis,differences)),len(labels))
    if solution is None:
        return None
    constant = origin_value
    for a,v in zip(solution,row(origin)):
        constant ^= field.mul(a,v)
    return constant,{label:a for label,a in zip(labels,solution) if a}


def drift_value(form, drift, x):
    xx = form.chunks(x)
    y = 0
    for (i,j),a in drift.items():
        y ^= form.field.mul(a,frob(form.field,xx[i],j))
    return y


def _enumerate_characters(form, drift, target, reduced):
    """Exact fallback with q scalar characters on the pinned affine chart."""
    f = form.field
    o, basis, _ = affine_domain(form.n,reduced)
    def val(z):
        return form.evaluate(z)^drift_value(form,drift,z)
    c = val(o)
    terms = [val(o^x)^c for x in basis]
    cross = [(i,j,form.polar(basis[i],basis[j])) for i,j in combinations(range(len(basis)),2)]
    total = 0
    for lam in range(f.size):
        sign = lambda x: f.trace(f.mul(lam,x))
        phase = (sign(c^target),sum(sign(x)<<i for i,x in enumerate(terms)),
                 frozenset((i,j) for i,j,x in cross if sign(x)))
        total += gauss(len(basis),phase)
    count, rem = divmod(total,f.size)
    if rem:
        raise ArithmeticError("inexact Fourier average")
    return count


def count(form, drift, target, pins=(), *, constant=0, point_count=None):
    f = form.field
    if not 0 <= target < f.size or not 0 <= constant < f.size:
        raise ValueError("target or affine constant outside field")
    terms = {}
    for (i,j),a in drift.items():
        if not 0 <= i < form.d or not isinstance(j,int) or not 0 <= a < f.size:
            raise ValueError("invalid Frobenius coefficient")
        # Choose minimum absolute degree representative and combine equivalent terms.
        exponent = j % f.m
        if 2*exponent > f.m:
            exponent -= f.m
        terms[i,exponent] = terms.get((i,exponent),0)^a
    terms = {z:a for z,a in terms.items() if a}
    target ^= constant
    checked = form._checks(target,pins)
    if checked is None:
        return 0
    reduced, dual = checked
    k = max((abs(j) for i,j in terms),default=0)
    if 2*k >= f.m:
        return _enumerate_characters(form,terms,target,reduced)
    rows = {}
    for (i,j),a in terms.items():
        y = frob(f,a,-j)
        row = f.trace_row(y) << (i*f.m)
        deg = 1 << (k-j)
        rows[deg] = rows.get(deg,0)^row
    vector_poly = {}
    for deg,row in rows.items():
        rem,vec = reduce_vector(row,form.polar_dual)
        if rem:
            raise ArithmeticError("trace-dual vector not represented")
        if vec:
            vector_poly[deg] = vec
    rhs = sum(c<<i for i,(_,c) in enumerate(reduced))
    if point_count is None:
        from torus_carry_count import point_count as backend
    else:
        backend = point_count
    q = f.size
    total = 0
    g = 1 << k
    for s in range(1 << len(reduced)):
        w = apply_basis(dual,s)
        vector = dict(vector_poly)
        vector[0] = w
        poly = {(g,2):1,(g,1):1,(2*g,0):target}
        def term(deg,value):
            poly[deg,0] = poly.get((deg,0),0)^value
        for i,a in vector.items():
            term(i+i,form.evaluate(a))
        for (i,a),(j,b) in combinations(vector.items(),2):
            term(i+j,form.polar(a,b))
        poly = {mon:c for mon,c in poly.items() if c}
        pts = backend(f,poly)
        if not isinstance(pts,int):
            raise TypeError("affine point-count backend must return an integer")
        bias = pts - (q if not form.evaluate(w) else 0) - (q-1)
        total += -bias if parity(s&rhs) else bias
    result, rem = divmod((1<<form.n)+form.bias*total,q<<len(reduced))
    if rem or not 0<=result<=1<<(form.n-len(reduced)):
        raise ArithmeticError("inconsistent affine point count for scalar fiber")
    return result


def check():
    from punctured_witness import BinaryField
    from scalar_field_pins import ScalarForm
    from random import Random
    rng = Random(45612)
    checked = 0
    for modulus in (7,11,37):
        f = BinaryField(modulus)
        form = ScalarForm(f,[1,2],{(0,1):1})
        cases = [{}, {(0,1):3,(1,-1):2}, {(0,2):1}, {(1,-2):3,(0,1):1}]
        pin0, pin1 = rng.sample(range(1,1<<form.n),2)
        for drift in cases:
            truth = [form.evaluate(x)^drift_value(form,drift,x)^2 for x in range(1<<form.n)]
            for pins in ((),((pin0,1),),((pin0,1),(pin0,1)),((pin0,1),(pin0,0)),
                         ((pin0,0),(pin1,1),(pin0^pin1,1))):
                expected = [0]*f.size
                for x,t in enumerate(truth):
                    if all(parity(x&v)==b for v,b in pins):
                        expected[t] += 1
                for t in (range(f.size) if f.m<5 else (0,1,12,31)):
                    assert count(form,drift,t,pins,constant=2,point_count=sparse_point_count)==expected[t]
                    checked += 1
        def dense_count(field,poly):
            value = sparse_point_count(field,poly)
            pts = 0
            for v,y in product(range(field.size),repeat=2):
                p = 0
                for (i,j),a in poly.items():
                    p ^= field.mul(a,field.mul(power(field,v,i),power(field,y,j)))
                pts += not p
            assert pts==value
            return pts
        if f.m==3:
            val = count(form,{(0,-1):1,(1,1):3},3,((pin0,1),),point_count=dense_count)
            assert val>=0
        if f.m==5:
            # x^4 has full binary rank on one field coordinate. It enters the
            # curve branch, as confirmed by a callback on this genuinely k=2 case.
            calls = []
            def observed(field,poly):
                calls.append(True)
                return sparse_point_count(field,poly)
            count(form,{(0,2):1},1,point_count=observed)
            assert calls
            o,bs,_ = affine_domain(form.n,[(pin0,1)])
            fn = lambda x: drift_value(form,{(0,2):1,(1,-1):3},x)^2
            c,ds = fit_affine(f,form.d,o,bs,fn(o),[fn(o^z)^fn(o) for z in bs],2)
            assert all((c^drift_value(form,ds,x))==fn(x) for x in range(1<<form.n)
                       if parity(x&pin0)==1)
    # Execute the public default on a signed negative-exponent input, while
    # tracking the actual native function (not substituting a numeric oracle).
    from unittest.mock import patch
    import torus_carry_count
    f = BinaryField(11)
    form = ScalarForm(f,[0,0],{(0,1):1})
    drift = {(0,-1):3}
    pins = ((3,1),)
    truth = sum((form.evaluate(x)^drift_value(form,drift,x))==0 and parity(x&3)
                for x in range(1 << form.n))
    with patch.object(torus_carry_count,"point_count",wraps=torus_carry_count.point_count) as native:
        assert count(form,drift,0,pins)==truth
        assert native.call_count==2
    print(f"{checked} exact target comparisons, explicit callbacks, affine fit and native default passed")


if __name__=="__main__":
    check()
