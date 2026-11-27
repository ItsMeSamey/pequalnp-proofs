"""Common translation-period basis for Boolean scalar ANFs, using integer bit masks."""
def difference_level(poly, shift, level):
    coefficients=set()
    for monomial in poly:
        moving=monomial & shift
        removed=moving
        while removed:
            term=monomial ^ removed
            if term.bit_count()==level:
                coefficients.symmetric_difference_update((term,))
            removed=(removed-1)&moving
    return coefficients

def common_period(polynomials, dimension):
    polynomials = tuple(tuple(poly) for poly in polynomials)
    if dimension<0 or any(m<0 or m>=1<<dimension for f in polynomials for m in f):
        raise ValueError("monomial outside chart coordinates")
    degree=max((m.bit_count() for f in polynomials for m in f),default=0)
    basis=[1<<i for i in range(dimension)]
    for level in reversed(range(degree)):
        equations={}
        indices={}
        kernel=[]
        for shift in basis:
            vector=0
            for coordinate,poly in enumerate(polynomials):
                for term in difference_level(poly,shift,level):
                    key=(coordinate,term)
                    vector ^= 1<<indices.setdefault(key,len(indices))
            while vector:
                pivot=vector.bit_length()-1
                if pivot not in equations:
                    equations[pivot]=(vector,shift)
                    break
                other,previous=equations[pivot]
                vector ^= other
                shift ^= previous
            if not vector:
                kernel.append(shift)
        basis=kernel
    return basis
