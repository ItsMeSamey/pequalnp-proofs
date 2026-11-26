"""Compare adaptive variable-pool conflict discovery with brute-force split trees."""
from functools import lru_cache
from itertools import combinations
from random import Random
from sympy import Matrix


def checker(rows, n, m):
    @lru_cache(None)
    def fits(ids):
        profiles = sorted({rows[u] for u in ids} - {0})
        if not profiles:
            return True
        a = Matrix([[int(bool(p & (1<<i))) for i in range(m)] for p in profiles])
        return a.rank() == a.row_join(Matrix.ones(len(profiles),1)).rank()

    @lru_cache(None)
    def obstruction(ids, pool, depth):
        if fits(ids):
            return None
        if not depth or not pool:
            small = list(ids)
            for u in ids:
                trial = tuple(v for v in small if v != u)
                if not fits(trial):
                    small = list(trial)
            assert len(small) <= m+1
            return frozenset(small)
        witnesses = set()
        for i in pool:
            rest = tuple(j for j in pool if j != i)
            for bit in (0,1):
                child = tuple(u for u in ids if u >> i & 1 == bit)
                conflict = obstruction(child, rest, depth-1)
                if conflict is not None:
                    witnesses.update(conflict)
                    break
            else:
                return None
        return frozenset(witnesses)

    ids = tuple(rows)
    all_vars = tuple(range(n))
    @lru_cache(None)
    def brute(s, pool, depth):
        if fits(s):
            return True
        return depth > 0 and any(
            all(brute(tuple(u for u in s if u >> i & 1 == b),
                      tuple(j for j in pool if j != i),depth-1) for b in (0,1))
            for i in pool)

    def search(k):
        @lru_cache(None)
        def extend(pool):
            conflict = obstruction(ids, pool, k)
            if conflict is None:
                return True
            assert not brute(tuple(sorted(conflict)), pool, k)
            if len(pool) == (1<<k)-1:
                return False
            choices = [i for i in all_vars if i not in pool and
                       len({u >> i & 1 for u in conflict}) == 2]
            return any(extend(tuple(sorted((*pool, i)))) for i in choices)
        return extend(())

    return search, lambda k: brute(ids, all_vars, k), fits


def main():
    rng = Random(1731)
    cases = 0
    for n in (2,3,4):
        for _ in range(12):
            rows = {u:rng.randrange(8) for u in range(1<<n) if rng.randrange(5)}
            search, brute, _ = checker(rows,n,3)
            for k in range(3):
                assert search(k) == brute(k)
                cases += 1
    print(f"{cases} adaptive depth decisions agreed with brute-force trees.")


if __name__ == '__main__':
    main()
