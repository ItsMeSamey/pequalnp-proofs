"""Unlabelled-output boundary parity signatures, after removing terminal edges."""
from itertools import combinations
from collections import Counter


def signature(n, edges):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    rows = [set() for _ in range(8)]
    for s in range(1 << n):
        q = sum(1 << v for v in range(n)
                if (s >> v) & 1 and (s & adj[v]).bit_count() % 2)
        if q < 8:
            rows[s & 7].add(q)
    pairs = (3, 5, 6)
    return (sum(1 << i for i, p in enumerate(pairs) if p in rows[p]),
            sum(1 << i for i, p in enumerate(pairs) if p in rows[7]))


def enumerate_small(k):
    best = {}
    for n in range(3, k+1):
        possible = [(u,v) for u,v in combinations(range(n),2) if v >= 3]
        for m in range(1 << len(possible)):
            es = [p for j, p in enumerate(possible) if (m>>j)&1]
            key = signature(n, es)
            if key not in best or (n,len(es)) < (best[key][0],len(best[key][1])):
                best[key] = (n, es)
    return best


if __name__ == '__main__':
    best = enumerate_small(6)
    print(len(best), Counter(p for p,q in best))
    for k,v in sorted(best.items()):
        if k[0] == 7:
            print(k,v)
    cases = {(p, (7 if p.bit_count() == 2 else p)) for p in range(7)}
    cases |= {(7, q) for q in range(8)}
    assert set(best) == cases and best[7,7][0] == 6
    representatives = [
        (4, [(0,3),(1,3),(2,3)], 0),
        (5, [(0,3),(1,3),(2,4),(3,4)], 1),
        (5, [(0,3),(0,4),(1,3),(2,4),(3,4)], 3),
        (6, [(0,3),(1,3),(0,4),(2,4),(1,5),(2,5)], 7),
    ]
    for n, edges, q in representatives:
        assert signature(n, edges) == (7, q)
