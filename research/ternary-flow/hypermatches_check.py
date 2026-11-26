"""Enumerate all boundary patterns and all exact-cover counts for a binary mod-3 star."""
from functools import lru_cache
from itertools import product


def counts(charge):
    allowed = [(a,b) for a,b in product(range(3),repeat=2) if (a-b)%3 == charge]
    terminals = list(range(6))
    hubs = [6,7]
    next_vertex = 8
    triples = []
    for a,b in allowed:
        ports = [t for t in terminals if t not in (a,3+b)] + hubs
        size = len(ports)
        q,r,f = [list(range(next_vertex+i*size,next_vertex+(i+1)*size)) for i in range(3)]
        next_vertex += 3*size
        for i,p in enumerate(ports):
            triples.extend([(p,q[i],r[i]),(q[i],r[i-1],f[i])])
        triples.extend(tuple(f[i:i+3]) for i in range(0,size,3))
    by_vertex = [[] for v in range(next_vertex)]
    for triple in triples:
        mask = sum(1 << v for v in triple)
        for v in triple:
            by_vertex[v].append(mask)

    @lru_cache(None)
    def solve(remaining):
        if not remaining:
            return 1
        options = min(([mask for mask in candidates if mask & remaining == mask]
                       for v,candidates in enumerate(by_vertex) if remaining >> v & 1),key=len)
        return sum(solve(remaining ^ mask) for mask in options)
    expected = {(1 << a) | (1 << (3+b)) for a,b in allowed}
    for deleted in range(64):
        assert solve(((1 << next_vertex)-1) ^ deleted) == (deleted in expected)
for charge in range(3):
    counts(charge)
print("All 192 boundary/charge pairs have exactly the prescribed number of exact covers.")
