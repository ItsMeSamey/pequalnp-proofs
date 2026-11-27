"""Polynomial identity testing on affine binomial models over a binary field.

nonzero(field,n,equations,polynomial) tests whether any model has nonzero
polynomial value. equations follow affine_binomial's paired (coefficient,
exponents) convention; polynomial is an iterable of terms in that same order.
All exponents are encoded integers, and no domain elements, supports, discrete
logarithms, or torsor representatives are enumerated. The number of HNF
queries is quadratic in polynomial sparsity, plus closure feasibility checks.
"""
from math import gcd
from sympy import Matrix,eye
from sympy.matrices.normalforms import hermite_normal_form
from affine_binomial import least_support_count,power


def primitive_combination(values,modulus):
    """Coefficients for a Bezout combination equal to one modulo modulus."""
    d=modulus
    weights=[]
    for s in values:
        t=gcd(d,s)
        v=pow(s//t,-1,d//t) if d//t>1 else 0
        u=(t-v*s)//d
        weights=[u*w%modulus for w in weights]+[v%modulus]
        d=t
    return weights if d==1 else None


def ratio(field,rows,constants,difference):
    """Return the forced x^difference on a nonempty torus fiber, else None."""
    N=field.size-1
    if N==1 or all(k%N==0 for k in difference):
        return 1
    if not rows:
        return None
    width=len(difference)
    height=len(rows)+1
    matrix=Matrix(height,width,[k%N for row in (*rows,difference) for k in row])
    basis=hermite_normal_form(matrix.row_join(N*eye(height)),D=N**height)
    annihilator=N*basis.inv()
    exponents=[]
    targets=[]
    for row in annihilator.tolist():
        product=1
        for c,a in zip(constants,row):
            product=field.mul(product,power(field,c,int(a)%N))
        targets.append(product)
        exponents.append(int(row[-1])%N)
    bezout=primitive_combination(exponents,N)
    if bezout is None:
        return None
    # Each HNF row imposes z^s=product^(-1); combine to isolate z.
    value=1
    for v,b in zip(targets,bezout):
        value=field.mul(value,power(field,v,(-b)%N))
    return value


def nonzero(field,n,equations,polynomial):
    if type(n) is not int or n<0:
        raise ValueError("invalid dimension")
    def term(t):
        c,ex=t
        ex=tuple(ex)
        if type(c) is not int or not 0<=c<field.size or len(ex)!=n or any(
                type(k) is not int or k<0 for k in ex):
            raise ValueError("invalid term")
        return c,ex
    eq=tuple(tuple(term(t) for t in pair) for pair in equations)
    if any(len(pair)!=2 for pair in eq):
        raise ValueError("expected two terms per binomial")
    coeffs={}
    for c,ex in map(term,polynomial):
        coeffs[ex]=coeffs.get(ex,0)^c
    one=(1,(0,)*n)
    groups={}
    closures={}
    for ex,c in coeffs.items():
        if not c:
            continue
        mask=tuple(i for i,v in enumerate(ex) if v)
        if mask not in closures:
            # On this torus x_i^N=1 is exactly the requirement x_i!=0.
            pins=tuple(((1,tuple((field.size-1)*int(i==j) for j in range(n))),one)
                       for i in mask)
            closures[mask]=least_support_count(field,n,(*eq,*pins))
        support,count=closures[mask]
        if count:
            groups.setdefault(support,[]).append((c,ex))

    # A zero character expansion on its least support stays zero on every
    # feasible extension: setting outside coordinates to zero gives a model
    # on the least support, and the group's monomials keep their values.
    # Conversely, restrict to an inclusion-minimal nonzero group; all strict
    # subgroups vanish there and incomparable/larger supports are inactive.
    for support,terms in groups.items():
        active=set(support)
        rows=[]
        constants=[]
        for (a,p),(b,q) in eq:
            if a and b and all(i in active or k==0 for i,k in enumerate(p)):
                rows.append(tuple(p[i]-q[i] for i in support))
                constants.append(field.mul(b,field.inverse(a)))
        classes=[]
        for c,ex in terms:
            powers=tuple(ex[i] for i in support)
            for j,(base,weight) in enumerate(classes):
                scale=ratio(field,rows,constants,tuple(v-w for v,w in zip(powers,base)))
                if scale is not None:
                    classes[j]=(base,weight^field.mul(c,scale))
                    break
            else:
                classes.append((powers,c))
        # Distinct characters of the finite odd-order kernel are linearly
        # independent over this characteristic-two field.
        if any(weight for _,weight in classes):
            return True
    return False


def self_test():
    from itertools import product
    from random import Random
    from punctured_witness import BinaryField
    rng=Random(318)
    tested=0
    for mod in (7,11,19):
        f=BinaryField(mod)
        for n in (0,1,2):
            for _ in range(24):
                def randterm():
                    return rng.randrange(f.size),tuple(rng.randrange(7) for _ in range(n))
                eq=[(randterm(),randterm()) for _ in range(rng.randrange(4))]
                poly=[randterm() for _ in range(rng.randrange(7))]
                def v(t,x):
                    a,ex=t
                    for y,k in zip(x,ex):
                        a=f.mul(a,power(f,y,k))
                    return a
                def val(x):
                    acc=0
                    for term in poly:
                        acc^=v(term,x)
                    return acc
                truth=any(all(v(a,x)==v(b,x) for a,b in eq) and val(x)
                          for x in product(range(f.size),repeat=n))
                assert nonzero(f,n,eq,poly)==truth
                tested+=1
    # x^3=c over GF16 has three torus solutions. Character ratio c on that
    # torsor cancels exactly with its coefficient, while x is nonconstant.
    f=BinaryField(19)
    c=power(f,2,3)
    eq=[((1,(3,)),(c,(0,)))]
    assert not nonzero(f,1,eq,[(3,(4,)),(f.mul(3,c),(1,))])
    assert nonzero(f,1,eq,[(3,(4,)),(f.mul(3,c)^1,(1,))])
    assert not nonzero(f,2,[((3,(1,0)),(7,(0,1)))],[(3,(1,0)),(7,(0,1))])
    # x^2=x and x!=0 distinguish the nonzero support from the origin.
    assert nonzero(f,1,[((1,(2,)),(1,(1,)))],[(1,(0,)),(1,(1,))])
    print(f"{tested} exhaustive model comparisons and coefficient/closure controls passed")


if __name__=='__main__':
    self_test()
