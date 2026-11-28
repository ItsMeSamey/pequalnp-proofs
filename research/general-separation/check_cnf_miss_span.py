"""Raw signed-CNF oracle: ranks of original truth columns by explicit XOR spans."""
from itertools import product
from cnf_miss_span import project, solve
RAW_MODE="enumerate"
IE_MODE="inclusion_exclusion"


def check(n,rows,expected_mode=None):
    used=sorted({abs(l) for c in rows for l in c})
    assignments=[{v for v,b in zip(used,bits) if b} for bits in product(range(2),repeat=len(used))]
    def miss(c,s):
        return not any((abs(l) in s)==(l>0) for l in c)
    columns=[sum(miss(c,s)<<j for j,s in enumerate(assignments)) for c in rows]
    span={0}
    for c in columns:
        span |= {b^c for b in span}
    models=[s for s in assignments if not any(miss(c,s) for c in rows)]
    basis=project(n,rows)
    assert list(basis.used)==used
    assert list(basis.clauses)==[basis.normalized[i] for i in basis.indices]
    assert 1<<len(basis.clauses)==len(span)
    subsetspan={0}
    for c in basis.clauses:
        col=sum(miss(c,s)<<i for i,s in enumerate(assignments))
        subsetspan |= {b^col for b in subsetspan}
    assert subsetspan==span
    assert [s for s in assignments if not any(miss(c,s) for c in basis.clauses)]==models
    ans=solve(n,rows)
    assert ans['rank']==len(basis.clauses)
    assert ans['status']==('nonzero' if models else 'zero')
    assert ans["count"]==(len(models),n-len(used))
    if models:
        assert set(ans['true_ids']) in models
        mantissa,shift=ans['count']
        assert shift==n-len(used) and mantissa==len(models)
    if expected_mode is not None:
        assert ans['mode']==expected_mode
        terms=ans['terms']
        assert terms>0
        denied=solve(n,rows,max_terms=terms-1)
        assert denied['status']=='unknown' and denied['required']==terms
        assert solve(n,rows,max_terms=terms)['count']==ans['count']
    return ans


def main():
    square=[(1,3,4),(-1,3,4),(2,3,4),(-2,3,4)]
    # Four distinct three-literal misses, all equal size, sum to zero over GF2.
    assert check(4,square)['rank']==3
    # Two long disjoint clauses force inclusion-exclusion even after pricing lifts.
    check(13,[(1,-2,3,-4,5),(6,7,-8,9,-10)],IE_MODE)
    rows=[tuple(-j if mask>>(j-1)&1 else j for j in range(1,4)) for mask in range(6)]
    check(3,rows,RAW_MODE)
    check(3,rows+[(-1,-2,-3),(1,-2,-3)])
    huge=1<<400
    check(huge,[(huge,huge),(2,-2),(-huge,5),(-huge,5)])
    check(0,[])
    check(0,[()])
    for flags in range(16):
        check(4,[c for j,c in enumerate(square) if flags>>j&1])
    print('Direct miss-vector ranks, retained models, original sparse witnesses and both budgets passed.')


if __name__=='__main__':
    main()
