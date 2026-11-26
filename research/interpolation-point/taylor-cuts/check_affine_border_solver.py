"""Independent Boolean evaluation checks for the clique-border solver."""
from itertools import combinations
from random import Random
from affine_border_solver import CliqueBudgetExceeded, _multiplication, solve_border
from affine_quadratic_span import _normalize


def check(n, flats, *, expected_cliques=None):
    models = [x for x in range(1<<n) if all(
        any((x&m).bit_count()%2 != t for m,t in f) for f in flats)]
    count,witness = solve_border(n,flats,max_cliques=128)
    assert count==len(models) and (witness in models if models else witness is None)
    norm = _normalize(n,flats)
    if () not in norm:
        basis,ops = _multiplication(n,norm,128)
        if expected_cliques is not None:
            assert len(basis)==expected_cliques
        for x in models:
            ev=sum((x&b==b)<<j for j,b in enumerate(basis))
            for i,rows in enumerate(ops):
                image=sum(((ev&r).bit_count()%2)<<j for j,r in enumerate(rows))
                assert image==(ev if x>>i&1 else 0)


if __name__=='__main__':
    rng=Random(433)
    for _ in range(260):
        n=rng.randrange(1,7)
        flats=[tuple((rng.randrange(1<<n),rng.randrange(2))
                     for j in range(rng.choice([1,2,2,2]))) for i in range(rng.randrange(20))]
        check(n,flats)
    for n in (4,6,8):
        for typ in ('bipartite','matching'):
            missing={(i,j) for i,j in combinations(range(n),2)
                     if (i<n//2<=j if typ=='bipartite' else i%2==0 and j==i+1)}
            # Lower-triangular coordinate changes retain leading pair pivots.
            coords=[(1<<i)|rng.randrange(1<<i) for i in range(n)]
            for _ in range(4):
                flats=[((coords[i],rng.randrange(2)),(coords[j],rng.randrange(2)))
                       for i,j in combinations(range(n),2) if (i,j) not in missing]
                check(n,flats,expected_cliques=1+n+len(missing))
    check(0,[]);check(0,[()]);check(3,[((1,0),),((1,1),)])
    check(3,[((1,0),(1,1)),((2,1),(4,1))])
    try:
        solve_border(12,[],max_cliques=50)
        raise AssertionError('expected a clique budget rejection')
    except CliqueBudgetExceeded:
        pass
    print('260 random systems, 24 signed transformed bipartite/matching fixtures, four edge cases, budget check passed')
