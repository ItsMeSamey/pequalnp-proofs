"""Exact two-label checks on a graph with crossing disjoint three-edge bonds."""
from itertools import product
from random import Random

EDGES = [(0,1),(1,2),(2,3),(2,3),(3,0),(3,0),(0,0)]
BONDS = [(1,4,5), (0,2,3)]

def trace(mask, endpoints):
    return sum(((mask >> e)&1)<<i for i,e in enumerate(endpoints))

def xor_labels(mask, weights):
    value = 0
    for i,w in enumerate(weights):
        if mask >> i & 1:
            value ^= w
    return value

def oracle_solutions(c,d,ts):
    p = c ^ (7 if c.bit_count()%2 else 0)
    classes = []
    for v in range(8):
        if (v ^ d) not in (0,7) or (v & p):
            continue
        classes.append(xor_labels(p,ts[0])^xor_labels(v,ts[1]))
    return set(classes)

def main():
    rng = Random(4117)
    scenarios = 0
    for attempt in range(12):
        tables = [([rng.randrange(4) for _ in range(3)],
                   [rng.randrange(4) for _ in range(3)]) for _ in BONDS]
        for shore in range(8):
            cut = sum((((shore>>a)^(shore>>b))&1)<<i for i,(a,b) in enumerate(EDGES))
            for cycle in range(1<<len(EDGES)):
                mod2 = 0
                for i,(a,b) in enumerate(EDGES):
                    if cycle>>i&1:
                        mod2 ^= (1<<a)^(1<<b)
                if mod2: continue
                pq = [(trace(cut,T),trace(cycle,T)) for T in BONDS]
                opts = [oracle_solutions(p,q,t) for (p,q),t in zip(pq,tables)]
                if any(not x for x in opts): continue
                real = {x^y for x,y in product(*opts)}
                canonical = 0
                optional = []
                weights4 = [0,0]
                for (p,q),(a,b) in zip(pq,tables):
                    u = p^(7 if p.bit_count()%2 else 0)
                    canonical ^= xor_labels(u,a)^xor_labels(q,b)
                    w = xor_labels(7,b)
                    for j in range(2):
                        if w>>j&1: weights4[j] += q.bit_count()
                    if not u: optional.append(w)
                canonical ^= sum(((k%4)//2)<<j for j,k in enumerate(weights4))
                actual = {canonical}
                for w in optional: actual |= {s^w for s in actual}
                assert real == actual
                assert any(not (cycle & (cut ^ flips)) for flips in (
                    sum(sum(1<<e for e in T) for j,T in enumerate(BONDS) if h>>j&1)
                    for h in range(4)))
                scenarios += 1
    print(f'{scenarios} crossing-bond label and normalization checks passed')

if __name__ == '__main__':
    main()
