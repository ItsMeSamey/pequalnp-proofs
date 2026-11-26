"""Direct truth tables for unrestricted degree-two ANFs and flat adapter agreement."""
from itertools import combinations
from random import Random
from affine_border_general import CliqueBudgetExceeded, solve_quadratic_anf
from affine_border_solver import solve_border


def check(n,rows):
    solutions=[]
    for x in range(1<<n):
        if all(sum(all(x>>i&1 for i in range(n) if m>>i&1) for m in row)%2==0 for row in rows):
            solutions.append(x)
    count,witness=solve_quadratic_anf(n,rows,max_cliques=128)
    assert count==len(solutions) and (witness in solutions if solutions else witness is None)
    return count


def flat_anf(n,flat):
    vals=[int(all((x&m).bit_count()%2==t for m,t in flat)) for x in range(1<<n)]
    for i in range(n):
        for x in range(1<<n):
            if x>>i&1:
                vals[x]^=vals[x^(1<<i)]
    return [m for m,v in enumerate(vals) if v]


if __name__=='__main__':
    rng=Random(2491)
    for _ in range(280):
        n=rng.randrange(7)
        mons=[m for m in range(1<<n) if m.bit_count()<=2]
        rows=[rng.choices(mons,k=rng.randrange(len(mons)+2)) for _ in range(rng.randrange(10))]
        check(n,rows)
    for _ in range(100):
        n=rng.randrange(1,6)
        flats=[[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(3))]
               for _ in range(rng.randrange(9))]
        rows=[flat_anf(n,f) for f in flats]
        assert check(n,rows)==solve_border(n,flats)[0]
    assert check(4,[[3,12]])==10  # Nondecomposable polar form of rank four.
    assert check(4,[[3,12],[3,12,0]])==0
    assert check(5,[[1,2,0],[1,2]])==0
    assert check(3,[[3,3,0,0]])==8
    assert check(0,[[]])==1 and check(0,[[0]])==0
    for n in (6,8):
        for missing in ({(i,j) for i in range(n//2) for j in range(n//2,n)},
                        {(i,i+1) for i in range(0,n,2)}):
            rows=[]
            lower=[]
            for i,j in sorted(combinations(range(n),2), key=lambda t:(1<<t[0])+(1<<t[1])):
                m=(1<<i)|(1<<j)
                if (i,j) in missing:
                    lower.append(m)
                else:
                    rows.append([m]+rng.sample(lower,min(2,len(lower)))+
                                [1<<rng.randrange(n)]*rng.randrange(2))
            check(n,rows)
    for row in ([-1],[7],[8]):
        try:solve_quadratic_anf(3,[row])
        except ValueError:pass
        else:raise AssertionError('invalid monomial accepted')
    try:solve_quadratic_anf(10,[],max_cliques=20)
    except CliqueBudgetExceeded:pass
    else:raise AssertionError('clique cap not enforced')
    print('280 arbitrary systems, 100 flat adapter comparisons, polar rank four, affine conflicts, duplicate terms, structured defects and validation passed')
