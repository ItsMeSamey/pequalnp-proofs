"""Exhaustive local extension checks and independent glued-space enumeration."""
from itertools import combinations
from functools import lru_cache
from random import Random

@lru_cache(maxsize=None)
def spaces(n):
    seen = {frozenset([0])}
    layer = seen.copy()
    while layer:
        new = {s.union(v ^ x for x in s) for s in layer
               for v in range(1, 1 << n) if v not in s} - seen
        seen.update(new)
        layer = new
    return tuple(seen)

def quadratic(n, mask):
    terms = [1 << i for i in range(n)]
    terms += [(1 << i) | (1 << j) for i, j in combinations(range(n), 2)]
    return [sum(1 for j,t in enumerate(terms) if mask >> j & 1 and x&t==t)%2
            for x in range(1<<n)]

def profile(q, private, shared):
    z = {i for i,t in enumerate(q) if t == 0}
    singular = [s for s in spaces(private+shared) if s<=z]
    result = {}
    for h in spaces(shared):
        candidates = [s for s in singular if {v>>private for v in s}<=h]
        onto = [s for s in candidates if {v>>private for v in s}==h]
        if onto:
            result[h] = max(len(s) for s in onto)
            assert result[h] == max(len(s) for s in candidates)
    return result

def main():
    for m in range(1024):
        profile(quadratic(4,m),2,2)
    rng = Random(53)
    for a,b,k,trials in [(1,1,2,100),(2,2,1,200),(1,2,2,100)]:
        for _ in range(trials):
            qa = quadratic(a+k,rng.getrandbits((a+k)*(a+k+1)//2))
            qb = quadratic(b+k,rng.getrandbits((b+k)*(b+k+1)//2))
            pa,pb = profile(qa,a,k),profile(qb,b,k)
            predicted = max(pa[h]*pb[h]//len(h) for h in pa.keys() & pb.keys())
            def accepts(x):
                h = x >> (a+b)
                return not (qa[(h<<a) | (x % (1<<a))]
                            or qb[(h<<b) | ((x>>a) % (1<<b))])
            good = {x for x in range(1<<(a+b+k)) if accepts(x)}
            assert predicted == max(len(s) for s in spaces(a+b+k) if s<=good)
    print("1024 local quadratic profiles and 400 joint fibers verified")

if __name__=="__main__":
    main()
