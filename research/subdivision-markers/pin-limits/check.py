"""Directly enumerate induced-even supports, then compare with a separate torso oracle."""
from itertools import combinations
from random import Random


def flood(rows, initial, allowed):
    visited = initial
    new = initial
    while new:
        frontier = 0
        while new:
            bit = new & -new
            frontier |= rows[bit.bit_length()-1]
            new ^= bit
        new = frontier & allowed & ~visited
        visited |= new
    return visited


def audit(rows, obs, check_robust=False):
    n = len(rows)
    universe = (1<<n)-1
    size = obs.bit_count()
    support = set()
    accepted = False
    robust = []
    for s in range(3,1<<n,4):
        odd = sum(1<<j for j in range(n) if (s>>j)&1 and (rows[j]&s).bit_count()%2)
        if not odd:
            support.add(s&obs)
        if not odd & ~obs:
            accepted = True
            robust.append((s&obs).bit_count())
    if accepted:
        assert min(robust) <= 2
    if not (rows[0]&2):
        assert 0 in support
        return

    reduced = rows.copy()
    reduced[0] ^= 2
    reduced[1] ^= 1
    visible = obs | 3
    torso = [reduced[i]&visible for i in range(n)]
    hidden = universe & ~visible
    while hidden:
        c = flood(reduced, hidden&-hidden,hidden)
        h = 0
        for v in range(n):
            if (c>>v)&1:
                h |= reduced[v]
        h &= visible
        for v in range(n):
            if (h>>v)&1:
                torso[v] |= h & ~(1<<v)
        hidden ^= c
    possible = []
    m = obs
    while True:
        closure = any(u&m==u for u in support)
        assert closure == bool(flood(torso,1,m|3)&2)
        possible.append(m)
        if not m:
            break
        m = (m-1)&obs

    if 0 in support:
        return
    minimal = [u for u in support if all(not (v!=u and (v&u)==v) for v in support)]
    trans = min(mask.bit_count() for mask in possible if all(mask&u for u in minimal))
    dp = {0:0}
    for u in minimal:
        for old,k in list(dp.items()):
            if not old&u:
                dp[old|u] = max(dp.get(old|u,0),k+1)
    assert max(dp.values()) == trans
    if 1 < min((x.bit_count() for x in minimal),default=0) < size:
        assert len(minimal) < __import__('math').comb(size,min(x.bit_count() for x in minimal)) or len({x.bit_count() for x in minimal})!=1


if __name__ == '__main__':
    rng = Random(87653)
    total = 0
    for n in range(2,6):
        es = list(combinations(range(n),2))
        for mask in range(1<<len(es)):
            rows = [0]*n
            for j,(a,b) in enumerate(es):
                if (mask>>j)&1:
                    rows[a] |= 1<<b
                    rows[b] |= 1<<a
            for obs in range(0,1<<n,4):
                audit(rows,obs)
                total += 1
    for i in range(1500):
        n = rng.randint(6,11)
        rows = [0]*n
        for a,b in combinations(range(n),2):
            if rng.random() < ((i%7)+1)/8:
                rows[a] |= 1<<b
                rows[b] |= 1<<a
        audit(rows,rng.randrange(1<<(n-2))<<2)
        total += 1
    print(total,'graph/observation masks passed')
