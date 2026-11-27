from itertools import combinations, product
from read_two_ring_nonzero import compile_nonzero
from ring_image_coordinate_2sat import coordinate_axes,solve


def span(basis):
    s={0}
    for v in basis:
        s |= {x^v for x in s}
    return s


def check_charts():
    pairs={frozenset(span((a,b))-{0}) for a,b in combinations(range(1,8),2)}
    spaces=[frozenset([i]) for i in range(1,8)]+list(pairs)
    bases=[set(B) for B in combinations(range(1,8),3) if len(span(B))==8]
    for k in range(5):
        for family in combinations(spaces,k):
            tests=[[(v,0) for v in sorted(s)[:2]] for s in family]
            if any(len(s)==3 for s in family):
                tests+=[[(v,1) for v in sorted(next(s for s in family if len(s)==3))[:2]]]
            expected=any(all(span(b&s)==set(s)|{0} for s in family) for b in bases)
            axes=coordinate_axes(tests)
            assert (axes is not None)==expected
            if axes is not None:
                assert len(span(axes))==1<<len(axes)
                assert all(span(set(axes)&s)==set(s)|{0} for s in family)


def check(n,rows,reason=None):
    r=compile_nonzero(n,rows)
    result=solve(*(r[k] for k in ('n','clauses','point','k')))
    models={x for x in product(range(2),repeat=n)
            if all(any(x[abs(i)-1]==(i>0) for i in row) for row in rows)}
    if reason:
        assert result==dict(status='unknown',reason=reason),result
    else:
        assert result['status']==('nonzero' if models else 'zero'),result
        if models:
            assert tuple(result['assignment']) in models


if __name__=='__main__':
    check_charts()
    check(2,[(1,2),(-1,2),(1,-2)],'nonflat_scope')
    check(3,[(1,2,3)],'codimension')
    for c in (1,-1):
        check(2,[(1,),(2,),(1,-2),(-1,2),(c,)])
    paired=[(sign*4,-u,-v) for u,v in combinations((1,2,3),2) for sign in (-1,1)]
    check(4,paired)
    check(4,paired+[(1,),(2,)])
    nae=[tuple(sign*i for i in triple) for triple in combinations(range(1,5),3)
         for sign in (-1,1)]
    check(4,nae,'incompatible_axes')
    # Three dependent lines, the quotient fixes x1=x2 and both values.
    for p in (1,-1):
        check(2,[(1,),(p*2,),(-1,2),(1,-2)])
    print('Basis enumeration, paired guard, conditional quotient and K4 NAE passed.')
