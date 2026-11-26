from random import Random
from sparse import solve, times, weighted_sum


def direct(rows, marker, weights):
    value = 0
    for x in range(1 << len(rows)):
        term = (x & marker).bit_count() % 2
        for i, (l,r) in enumerate(weights):
            factor = (0 if x >> i & 1 else l) ^ (0 if (x & rows[i]).bit_count() % 2 else r)
            term = times(term, factor)
        value ^= term
    return value


def check():
    rng = Random(442)
    for trial in range(240):
        n = trial % 6
        rows = [rng.randrange(1<<n) for _ in range(n)]
        h = rng.randrange(1<<n)
        weights = [(rng.randrange(8), rng.randrange(8)) for _ in rows]
        assert weighted_sum(rows,h,weights) == direct(rows,h,weights)
        models = [x for x in range(1<<n) if (x&h).bit_count()%2 and
                  all(not (x>>i&1) or (x&r).bit_count()%2==0 for i,r in enumerate(rows))]
        nonzero = 0
        for s in range(1<<n):
            w = [(0,1) if s>>i&1 else (1,0) for i in range(n)]
            nonzero += direct(rows,h,w)
        assert bool(models) == bool(nonzero)
        found = solve(rows,h,max(1,nonzero))
        assert (found in models) if models else (found is None)
    print("240 polynomial evaluations, full coefficient supports, and witness searches passed")


if __name__ == '__main__':
    check()
