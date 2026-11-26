"""Independent decision and original-witness replay. Run under pnp-native-search.lock."""
from itertools import product
from pathlib import Path
from random import Random
import sys
from affine_cover_solver import solve


def ok(x, flats, seed):
    def eq(pair):
        m, b = pair
        return (x & m).bit_count() % 2 == b
    return all(map(eq, seed)) and not any(all(map(eq, flat)) for flat in flats)


def check(n, flats, seed=(), **options):
    target = next((x for x in range(1 << n) if ok(x, flats, seed)), None)
    result = solve(n, flats, seed, **options)
    if isinstance(result, (list, tuple)) and len(result)==n and all(bit in (0,1) for bit in result):
        result=sum(bit<<i for i,bit in enumerate(result))
    assert (result is None) == (target is None), (n, flats, seed, result, target)
    if result is not None:
        assert isinstance(result,int) and 0 <= result < 1<<n and ok(result,flats,seed), (n,flats,seed,result)
    return 1


def main():
    cases=0
    for n in range(1,4):
        forms=[(m,b) for m in range(1<<n) for b in (0,1)]
        for a,b in product(forms,repeat=2):
            cases+=check(n,[[a,b]],(a,))
            cases+=check(n,[[a],[b]])
    cases+=check(0,[])
    cases+=check(0,[[]])
    rng=Random(290113)
    for _ in range(1100):
        n=rng.randrange(1,10)
        eq=lambda:(rng.randrange(1<<n),rng.randrange(2))
        seed=[eq() for _ in range(rng.randrange(4))]
        flats=[[eq() for _ in range(rng.randrange(1,5))] for _ in range(rng.randrange(12))]
        cases+=check(n,flats,seed)
    # Same plane in three different presentations. Its forbidden RHS
    # patterns leave only 11; the fourth flat makes the gate impossible.
    parallel=[[(1,0),(2,0)],[(1,0),(3,1)],[(2,0),(3,1)]]
    cases+=check(2,parallel)
    cases+=check(2,parallel+[[(1,1),(2,1)]])
    # A private coordinate appears only in the last constraint, but the
    # remaining core can forbid either all points or all except 11.
    private=[[(5,0),(2,1)]]
    cases+=check(3,parallel+private)
    cases+=check(3,parallel+[[(1,1),(2,1)]]+private)
    # Sparse packing relative to d vs full packing; both satisfiable and
    # collectively inconsistent rank-j constraints. Raw bits are kept.
    branches=set()
    def trace(frame,event,arg):
        if event=="line" and frame.f_code.co_name=="search" and "full" in frame.f_locals:
            branches.add((frame.f_locals["rank"],frame.f_locals["full"]))
        return trace
    sys.settrace(trace)
    for j in (2,3,4):
        for n,r in [(3*j,1),(2*j,2)]:
            groups=[[1<<(i*j+t) for t in range(j)] for i in range(r)]
            flats=[[(m,1) for m in g] for g in groups]
            cases+=check(n,flats,kernels=False)
            flats += [list(zip(groups[0],p)) for p in product(range(2),repeat=j)]
            cases+=check(n,flats,kernels=False)
    sys.settrace(None)
    assert {(j,flag) for j in (2,3,4) for flag in (False,True)} <= branches, branches
    print('Observed full-pattern and cover branches at ranks 2,3,4.')
    message=f'{cases} source-equation decision/witness comparisons passed. Both branch modes observed at ranks 2, 3 and 4.'
    print(message)
    Path(__file__).with_suffix('.result').write_text(message+'\n')


if __name__=='__main__':
    main()
