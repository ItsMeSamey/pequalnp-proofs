"""Deterministic affine zero counting in two variables over GF(2^m).

point_count(field, poly) accepts {(i,j): coefficient} in field coordinates.
Time is polynomial in m and the numerical coordinate degrees for fixed arity.
The direct sparse carry implementation favors clarity over practical speed.
It never lists all field elements or constructs a Teichmuller lift.
"""
from itertools import product
from math import comb


class Ring:
    """(Z/2^precision)[z]/g, where g is a monic 0/1 lift of the field modulus."""
    def __init__(self, modulus, precision):
        self.m = modulus.bit_length()-1
        self.mask = (1 << precision)-1
        self.tail = tuple(i for i in range(self.m) if (modulus >> i)&1)
        self.zero = (0,)*self.m
        self.one = (1,)+(0,)*(self.m-1)

    def lift(self, a):
        return tuple((a >> i)&1 for i in range(self.m))

    def add(self, a, b):
        return tuple((v+w)&self.mask for v,w in zip(a,b))

    def scale(self, a, t):
        return tuple((v*t)&self.mask for v in a)

    def mul(self, a, b):
        if a == self.one:
            return b
        if b == self.one:
            return a
        c = [0]*(2*self.m-1)
        for i,v in enumerate(a):
            if v:
                for j,w in enumerate(b):
                    c[i+j] += v*w
        for i in range(2*self.m-2,self.m-1,-1):
            top = c[i]&self.mask
            if top:
                for j in self.tail:
                    c[i-self.m+j] -= top
        return tuple(v&self.mask for v in c[:self.m])


def accumulate(table, key, value, ring):
    total = ring.add(table.get(key,ring.zero),value)
    if total != ring.zero:
        table[key] = total
    else:
        table.pop(key,None)


def poly_mul(f, g, ring):
    result = {}
    for a,u in f.items():
        for b,v in g.items():
            key = tuple(i+j for i,j in zip(a,b))
            accumulate(result,key,ring.mul(u,v),ring)
    return result


def carry_trace(polynomials, ring, arity):
    """Sum of coefficient products over all closed cyclic binary carries."""
    if any(not p for p in polynomials):
        return ring.zero
    # Each cyclic carry is a weighted average of m digits (local exponents).
    lo = tuple(min(e[j] for p in polynomials for e in p) for j in range(arity))
    hi = tuple(max(e[j] for p in polynomials for e in p) for j in range(arity))
    transitions = []
    for p in polynomials:
        group = {}
        for e,c in p.items():
            group.setdefault(tuple(i&1 for i in e),[]).append((e,c))
        transitions.append(group)
    total = ring.zero
    for start in product(*(range(a,b+1) for a,b in zip(lo,hi))):
        current = {start:ring.one}
        for level,group in enumerate(transitions):
            nxt = {}
            power = 1 << (len(transitions)-level-1)
            for state,w in current.items():
                for e,c in group.get(tuple(i&1 for i in state),()):
                    dest = tuple((i+j)//2 for i,j in zip(state,e))
                    # Future digits must sum to power*start - dest (dyadic weights).
                    if all((power-1)*l <= power*s-d <= (power-1)*h
                           for l,h,s,d in zip(lo,hi,start,dest)):
                        accumulate(nxt,dest,ring.mul(w,c),ring)
            current = nxt
            if not current:
                break
        total = ring.add(total,current.get(start,ring.zero))
    return total


def indicator_coefficients(precision):
    """First precision powers vanish. Remaining terms are ordinary integers."""
    degree = 2*precision-1
    coeffs = [0]*(degree+1)
    for j in range(precision,degree+1):
        for v in range(degree-j+1):
            coeffs[j+v] += (-1 if v&1 else 1)*comb(degree,j)*comb(degree-j,v)
    return coeffs


def torus_count(field, polynomial, arity):
    """Inputs here use a polynomial-basis field and tuple exponents of length arity."""
    q, m = field.size, field.m
    size = (q-1)**arity
    if not polynomial:
        return size
    if len(polynomial)==1:
        return 0
    precision = arity*m+1
    ring = Ring(field.modulus,precision)
    base = []
    residues = dict(polynomial)
    for _ in range(m):
        base.append({e:ring.lift(a) for e,a in residues.items()})
        residues = {e:field.mul(a,a) for e,a in residues.items()}
    powers = [{(0,)*arity:ring.one} for _ in range(m)]
    total = ring.zero
    coeffs = indicator_coefficients(precision)
    for k,coeff in enumerate(coeffs[1:],1):
        powers = [poly_mul(a,b,ring) for a,b in zip(powers,base)]
        if coeff & ring.mask:
            total = ring.add(total,ring.scale(carry_trace(powers,ring,arity),coeff))
    values = ring.scale(total,size)
    if any(values[1:]):
        raise ArithmeticError("non-scalar residue after unit indicator")
    number = (size-values[0])&ring.mask
    if number>size:
        raise ArithmeticError("torus count outside cardinality")
    return number


def point_count(field, polynomial):
    """Count affine zeros of a sparse bivariate polynomial over the supplied field."""
    polynomial = dict(polynomial)
    for e,a in polynomial.items():
        if len(e)!=2 or any(not isinstance(i,int) or i<0 for i in e):
            raise ValueError("invalid bivariate exponent")
        if not isinstance(a,int) or not 0<=a<field.size:
            raise ValueError("invalid field coefficient")
    polynomial = {e:a for e,a in polynomial.items() if a}
    if not hasattr(field,"modulus"):
        from punctured_chart_witness import power_chart
        chart = power_chart(field.m,1,field.mul)
        field = chart.field
        polynomial = {e:chart.encode(a) for e,a in polynomial.items()}
    result = int((0,0) not in polynomial)
    for axis in range(2):
        univariate = {(e[axis],):a for e,a in polynomial.items() if e[1-axis]==0}
        result += torus_count(field,univariate,1)
    return result+torus_count(field,polynomial,2)


def check():
    from random import Random
    from punctured_witness import BinaryField
    from frobenius_drift import power
    rng = Random(803)
    f = BinaryField(7)
    cases = [{},{(0,0):2},{(1,1):1},{(1,0):1,(0,1):1},
             {(0,0):1,(2,0):2,(0,2):3,(1,1):1},
             {(1,2):1,(1,1):1,(2,0):3,(0,0):2}]
    for _ in range(5):
        exps=rng.sample([(0,0),(0,1),(1,0),(0,2),(1,1)],3)
        cases.append({e:rng.randrange(1,4) for e in exps})
    def exhaustive(field,polynomial):
        count=0
        for x,y in product(range(field.size),repeat=2):
            v=0
            for (i,j),a in polynomial.items():
                v ^= field.mul(a,field.mul(power(field,x,i),power(field,y,j)))
            count+=not v
        return count
    for p in cases:
        assert point_count(f,p)==exhaustive(f,p)
    g=BinaryField(11)
    for p in ({(1,0):3,(0,1):6},{(2,0):3,(0,0):6}):
        assert point_count(g,p)==exhaustive(g,p)
    # Isolate cyclic carry trace from the unit indicator. Independent enumeration
    # includes general signed coefficients in the ring, not merely field lifts.
    for _ in range(40):
        m=3
        ring=Ring(11,5)
        polys=[]
        for j in range(m):
            polys.append({(rng.randrange(-2,4),rng.randrange(-2,4)):
                          tuple(rng.randrange(32) for _ in range(m)) for k in range(4)})
        expected=ring.zero
        for terms in product(*(p.items() for p in polys)):
            weighted=[sum((e[j]<<i) for i,(e,c) in enumerate(terms)) for j in range(2)]
            if all(v%7==0 for v in weighted):
                weight=ring.one
                for e,c in terms:
                    weight=ring.mul(weight,c)
                expected=ring.add(expected,weight)
        assert carry_trace(polys,ring,2)==expected
    print("13 affine counts and 40 independent cyclic carry traces passed")


if __name__=="__main__":
    check()
