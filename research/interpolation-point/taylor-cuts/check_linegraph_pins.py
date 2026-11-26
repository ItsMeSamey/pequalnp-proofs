"""Exhaustive verification; use brute force only for the general-factor oracle."""
from itertools import combinations
from random import Random
from collections import Counter

def submasks(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            return
        sub = (sub - 1) & mask

def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit

def factor(n, edges, available, pins, odd):
    incidence = [sum(1<<i for i in indices(available) if v in edges[i]) for v in range(n)]
    optional = available ^ pins
    allowed = []
    for inc in incidence:
        forced_degree = (inc & pins).bit_count()
        allowed.append({k for k in range((inc & optional).bit_count()+1)
                        if k+forced_degree == 0 or (k+forced_degree)%2 == odd})
    for chosen in submasks(optional):
        if all((inc & chosen).bit_count() in ds for inc, ds in zip(incidence,allowed)):
            return pins | chosen
    return None

def solve(n, edges, neighbors, pins):
    good, bad = [], []
    remaining = pins
    while remaining:
        part = remaining & -remaining
        while True:
            nxt = part
            for i in indices(part):
                nxt |= neighbors[i] & pins
            if nxt == part:
                break
            part = nxt
        remaining ^= part
        (bad if any((neighbors[i] & part).bit_count()%2 for i in indices(part)) else good).append(part)
    if not bad:
        return True, pins
    if len(bad)>1:
        return False, None
    for pieces in submasks((1<<len(good))-1):
        isolated = sum(good[j] for j in indices(pieces))
        available = (1<<len(edges))-1
        for i in indices(isolated):
            available &= ~(neighbors[i] | (1<<i))
        for odd in (False, True):
            extra = factor(n, edges, available, pins ^ isolated, odd)
            if extra is not None:
                return True, isolated | extra
    return True, None

def verify(n, edges, counts):
    neighbors = [sum(1<<j for j,f in enumerate(edges) if e!=f and set(e)&set(f)) for e in edges]
    solutions = {s for s in range(1<<len(edges))
                 if all((neighbors[j]&s).bit_count()%2==0 for j in indices(s))}
    for k in (3,4,5):
        for p in combinations(range(len(edges)),k):
            pins = sum(1<<i for i in p)
            covered, witness = solve(n,edges,neighbors,pins)
            if not covered:
                assert k>=4
                continue
            exists = any(s&pins==pins for s in solutions)
            assert exists==(witness is not None)
            if exists:
                assert witness in solutions and witness&pins==pins
            counts[k,exists]+=1

if __name__ == '__main__':
    counts=Counter()
    for n in range(2,6):
        candidates=list(combinations(range(n),2))
        for mask in range(1<<len(candidates)):
            verify(n,[candidates[i] for i in indices(mask)],counts)
    rng=Random(44029)
    for _ in range(90):
        candidates=list(combinations(range(6),2))
        verify(6,rng.sample(candidates,rng.randint(4,9)),counts)
    print(sorted(counts.items()))
