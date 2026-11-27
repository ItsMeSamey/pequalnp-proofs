"""Exact additive character sums on a binary field's multiplicative group.

character_sum(field,{e:a_e}) returns sum over nonzero x of (-1)^Tr(f(x)).
kloosterman(field,d) specializes f=x+d/x and uses the Hasse bound. A native
scalar-curve callback is supplied by point_count(field,d). No field elements
are enumerated. Work is polynomial in m and the *numerical* Laurent exponent
span including zero. Large binary-encoded exponents need not be inexpensive.
A user-supplied transition cap raises CarryBudgetExceeded on exhaustion.
"""
from math import comb,isqrt
from torus_carry_count import Ring,accumulate,indicator_coefficients


class CarryBudgetExceeded(RuntimeError):
    pass


def _sum(field,poly,bound,max_transitions):
    if max_transitions is not None and (type(max_transitions) is not int or max_transitions<0):
        raise ValueError("invalid transition budget")
    if any(type(e) is not int or type(a) is not int or not 0<=a<field.size for e,a in poly.items()):
        raise ValueError("invalid Laurent term")
    poly={e:a for e,a in poly.items() if a}
    q=field.size
    if not poly or set(poly)=={0}:
        return -(q-1) if field.trace(poly.get(0,0)) else q-1
    if not hasattr(field,"modulus"):
        from punctured_chart_witness import power_chart
        chart=power_chart(field.m,1,field.mul)
        field=chart.field
        poly={e:chart.encode(a) for e,a in poly.items()}
    # Recover the signed sum in [-bound,bound]. The indicator needs one
    # fewer bit because sign=1-2*indicator.
    precision=(2*bound).bit_length()
    ring=Ring(field.modulus,precision-1)
    coeffs=indicator_coefficients(precision-1)
    degree=max(i for i,c in enumerate(coeffs) if c & ring.mask)
    coeffs=coeffs[:degree+1]
    lo=min(0,min(poly))*degree
    hi=max(0,max(poly))*degree
    # Each layer chooses b summands from that Frobenius layer. Transitions
    # are indexed by parity of the source carry and by new total power.
    layers=[]
    for _ in range(field.m):
        base={e:ring.lift(a) for e,a in poly.items()}
        powers=[{0:ring.one}]
        for _ in range(degree):
            nxt={}
            for e,a in powers[-1].items():
                for j,b in base.items():
                    accumulate(nxt,e+j,ring.mul(a,b),ring)
            powers.append(nxt)
        options=[]
        for k in range(degree+1):
            by_parity=[[],[]]
            for b,terms in enumerate(powers[:degree-k+1]):
                binomial=comb(k+b,b)&ring.mask
                if binomial:
                    for e,a in terms.items():
                        c=ring.scale(a,binomial)
                        if c!=ring.zero:
                            by_parity[e&1].append((k+b,e,c))
            options.append(by_parity)
        layers.append(options)
        poly={e:field.mul(a,a) for e,a in poly.items()}
    total=ring.zero
    ticks=0
    for start in range(lo,hi+1):
        states={(0,start):ring.one}
        for level,options in enumerate(layers):
            nxt={}
            remaining=1<<(field.m-1-level)
            for (k,r),w in states.items():
                for power,e,c in options[k][r&1]:
                    ticks+=1
                    if max_transitions is not None and ticks>max_transitions:
                        raise CarryBudgetExceeded("Laurent carry transition budget exhausted")
                    dest=(r+e)//2
                    if (remaining-1)*lo<=remaining*start-dest<=(remaining-1)*hi:
                        accumulate(nxt,(power,dest),ring.mul(w,c),ring)
            states=nxt
            if not states:
                break
        for (k,r),w in states.items():
            if r==start and coeffs[k]:
                total=ring.add(total,ring.scale(w,coeffs[k]))
    summed=ring.scale(total,q-1)
    if any(summed[1:]):
        raise ArithmeticError("character sum did not reduce to a scalar")
    modulus=1<<precision
    result=(q-1-2*summed[0])%modulus
    if result>bound:
        result-=modulus
    if not -bound<=result<=bound:
        raise ArithmeticError("character sum outside certified interval")
    return result


def character_sum(field,polynomial,*,max_transitions=None):
    return _sum(field,dict(polynomial),field.size-1,max_transitions)


def kloosterman(field,d,*,max_transitions=None):
    if not 0<d<field.size:
        raise ValueError("nonzero field parameter required")
    return _sum(field,{1:1,-1:d},min(field.size-1,isqrt(4*field.size)),max_transitions)


def point_count(field,d):
    return field.size+1+kloosterman(field,d)


def self_test():
    from random import Random
    from punctured_witness import BinaryField
    rng=Random(137)
    checked=0
    for mod in (7,11,19):
        f=BinaryField(mod)
        def brute(p):
            total=0
            for x in range(1,f.size):
                y=0
                for e,c in p.items():
                    v=1
                    base=x if e>=0 else f.inverse(x)
                    for _ in range(abs(e)):
                        v=f.mul(v,base)
                    y^=f.mul(c,v)
                total+=1-2*f.trace(y)
            return total
        if f.m==2:
            from itertools import product
            for coefficients in product(range(f.size),repeat=3):
                p=dict(zip((-1,0,1),coefficients))
                assert character_sum(f,p)==brute(p)
                checked+=1
        for d in range(1,f.size):
            assert kloosterman(f,d)==brute({1:1,-1:d})
            checked+=1
        for _ in range(4):
            p={e:rng.randrange(f.size) for e in (-2,-1,0,1,3)}
            assert character_sum(f,p)==brute(p)
            checked+=1
    try:
        kloosterman(f,1,max_transitions=0)
    except CarryBudgetExceeded:
        pass
    else:
        raise AssertionError("zero carry budget ignored")
    print(f"{checked} exact Laurent sums matched direct enumeration")


if __name__=="__main__":
    self_test()
