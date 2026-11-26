"""Check homogeneous flattening, including empty neutral and absorbing leaves."""
from itertools import product
from random import Random

def run(types, labels, edges, fixed):
    n = len(edges)
    keep = {0} | {i for i,l in enumerate(labels) if l not in fixed}
    for u, branches in enumerate(edges):
        for es in branches:
            keep.update(v for v in es if v<n and types[u] != types[v])
    def summary(u, b):
        stops = set()
        todo = list(edges[u][b])
        while todo:
            v = todo.pop()
            if v>=n or v in keep:
                stops.add(v)
            else:
                assert types[u] == types[v]
                todo.extend(edges[v][fixed[labels[v]]])
        return stops
    compressed = [[summary(u,b) for b in (0,1)] for u in range(n)]
    for raw in product((0,1),repeat=2):
        bits = [fixed.get(i,raw[i]) for i in (0,1)]
        direct = {n:False,n+1:True}
        flat = direct.copy()
        for u in reversed(range(n)):
            op = all if types[u] else any
            b = bits[labels[u]]
            direct[u] = op(direct[v] for v in edges[u][b])
            flat[u] = op(flat[v] for v in compressed[u][b])
            assert flat[u] == direct[u]
            # Encode the selected gate equivalence, checking its potentially wide clause.
            values = [flat[v] for v in compressed[u][b]]
            for y in (False,True):
                local = all(y <= x for x in values) if types[u] else all(x <= y for x in values)
                wide = (y or not all(values)) if types[u] else (not y or any(values))
                even, odd = int(local), int(local and not wide)
                assert even-odd == int(y == direct[u])

rng = Random(8147)
for _ in range(2400):
    n = rng.randrange(1,9)
    types = [rng.getrandbits(1) for _ in range(n)]
    labels = [rng.randrange(2) for _ in range(n)]
    edges = [[tuple(v for v in range(u+1,n+2) if rng.random()<.35)
              for _ in (0,1)] for u in range(n)]
    for fixed in ({},{0:0},{0:1},{1:0},{1:1},{0:0,1:1}):
        run(types,labels,edges,fixed)
print('2400 seeded alternating DAGs × 6 restrictions; all states and both candidate output bits passed')
