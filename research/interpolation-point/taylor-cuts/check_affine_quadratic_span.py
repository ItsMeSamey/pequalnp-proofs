"""Direct Boolean checks for quadratic-span and covered-fiber solvers."""
from itertools import combinations,product
from random import Random
from affine_quadratic_span import (IncompleteQuadraticSpan,quadratic_cover,
                                  solve_quadratic,solve_quadratic_full)


def check(n,flats):
    valid = {x for x in range(1<<n) if all(
        not all((x&a).bit_count()%2==b for a,b in flat) for flat in flats)}
    cover = quadratic_cover(n,flats)
    for c in (None,cover):
        count,witness = solve_quadratic(n,flats,c)
        assert count==len(valid) and ((witness in valid) if valid else witness is None)
    try:
        count,witness = solve_quadratic_full(n,flats)
    except IncompleteQuadraticSpan:
        assert cover
        return False
    assert count==len(valid) and ((witness in valid) if valid else witness is None)
    assert count <= n+1
    return True


def main():
    rng = Random(523497)
    full = total = 0
    for n in range(4):
        pairs=list(combinations(range(n),2))
        for opts in product(range(-1,4),repeat=len(pairs)):
            flats=[((1<<i,b&1),(1<<j,b>>1)) for (i,j),b in zip(pairs,opts) if b>=0]
            full += check(n,flats)
            total += 1
    for n in (2,3,4,5):
        for _ in range(60):
            flats=[]
            for _ in range(rng.randrange(n*n+1)):
                flats.append(tuple((rng.randrange(1<<n),rng.randrange(2))
                                   for _ in range(rng.choice((1,2,2)))))
            full += check(n,flats)
            total += 1
    for n in range(6):
        for flats in ([()], [((0,1),)], [((0,0),(0,1))]):
            full += check(n,flats)
            total += 1
    n=5
    star=[((1<<i,1),(1<<j,1)) for i,j in combinations(range(1,n),2)]
    assert solve_quadratic(n,star,(0,))[0]==2*n
    try:
        solve_quadratic(n,star,(1,))
    except ValueError:
        pass
    else:
        raise AssertionError("invalid supplied cover accepted")
    print(total, "signed systems;",full,"full solver returns;",total-full,"rank defects; one explicit cover")
if __name__=='__main__':
    main()
