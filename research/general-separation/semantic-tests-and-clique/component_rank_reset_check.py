"""Verify local feedback ranks with reset to Boolean reachability on exit."""
from itertools import product
from random import Random

def check(rows,parts,feedback):
    n = len(rows)
    h = [sum(p==parts[i] and j in feedback for j,p in enumerate(parts)) for i in range(n)]
    def paths(u,seen):
        if u==n:
            return [()]
        if u in seen:
            return []
        return [(u,)+tail for v in rows[u] for tail in paths(v,seen|{u})]
    correct = tuple(min([h[i]+1]+[sum(parts[v]==parts[i] and v in feedback for v in path)
                                  for path in paths(i,set())]) for i in range(n))
    matches = []
    for vec in product(*(range(cap+2) for cap in h)):
        def cost(u,v):
            if v==n:
                rest = 0
            elif parts[v]==parts[u]:
                rest = vec[v]
            else:
                rest = 0 if vec[v]<=h[v] else h[u]+1
            return min(h[u]+1,rest+(u in feedback))
        if all(vec[u]==min([h[u]+1]+[cost(u,v) for v in rows[u]]) for u in range(n)):
            matches.append(vec)
    assert matches == [correct]

rng = Random(7110)
for _ in range(450):
    parts = [0,0,1,1]
    feedback = {i for i in range(4) if rng.randrange(2)}
    rows = [[v for v in range(5) if (v==4 or parts[v]>parts[i] or
             (parts[v]==parts[i] and (v>i or i in feedback or v in feedback)))
             and rng.randrange(2)] for i in range(4)]
    check(rows,parts,feedback)
check([[0,1],[1,2],[2,3],[3,4]],list(range(4)),set(range(4)))
print('450 seeded graphs and a four-cyclic-component forced chain passed')
