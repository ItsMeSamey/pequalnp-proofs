"""Check first-hit minima and Bellman ranks using exact reverse label reachability."""
from itertools import combinations_with_replacement, product
from random import Random

def reached(edges, start, terminal, label, stops):
    work = [(u, table[label]) for u,v,table in edges if v==terminal]
    seen = set()
    hits = set()
    while work:
        u,r = work.pop()
        if (u,r) in seen:
            continue
        seen.add((u,r))
        if u == start:
            hits.add(r)
        if u not in stops:
            work.extend((v,t[r]) for v,w,t in edges if w==u)
    return hits

def run(edges,n,inf):
    if any(r in reached(edges,u,u,r,set()) for u in range(n) for r in range(inf)):
        return False
    expected = tuple(min({inf}|reached(edges,u,n,0,set())) for u in range(n))
    def solutions(edges, nodes):
        ans = []
        for raw in product(range(inf+1),repeat=len(nodes)):
            ranks = dict(zip(nodes,raw))
            ranks[n] = 0
            if all(ranks[u] == min([inf]+[t[ranks[v]] for a,v,t in edges if a==u])
                   for u in nodes):
                ans.append(raw)
        return ans
    assert solutions(edges,list(range(n))) == [expected]
    for mask in range(1,1<<n):
        keep = [u for u in range(n) if mask>>u&1]
        reduced = []
        for u in keep:
            for v in keep+[n]:
                table = tuple(min({inf}|reached(edges,u,v,r,set(keep))) for r in range(inf+1))
                if min(table)<inf:
                    reduced.append((u,v,table))
        assert solutions(reduced,keep) == [tuple(expected[u] for u in keep)]
        assert not any(r in reached(reduced,u,u,r,set()) for u in keep for r in range(inf))
    return True

rng = Random(1447)
inf = 3
tables = [s+(inf,) for s in combinations_with_replacement(range(inf+1),inf)]
valid = 0
for _ in range(1000):
    edges = [(u,v,rng.choice(tables)) for u in range(3) for v in range(4) if rng.randrange(3)==0]
    valid += run(edges,3,inf)
print(valid,'graphs with no finite tight cycle passed every retained subset')
