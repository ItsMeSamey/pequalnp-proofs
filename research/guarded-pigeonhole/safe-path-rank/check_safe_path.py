"""Independent path enumeration and witness replay."""
from random import Random
from safe_path_rank import solve

def brute(edges, pairs, s, t):
    def visit(v, seen, chosen):
        if v == t:
            return True
        for i, (u,w) in enumerate(edges):
            if v not in (u,w):
                continue
            nxt = w if v == u else u
            if nxt in seen:
                continue
            if any(({i} | chosen) >= set(pair) for pair in pairs):
                continue
            if visit(nxt, seen | {nxt}, chosen | {i}):
                return True
        return False
    return visit(s, {s}, set())

rng = Random(62197)
for _ in range(1200):
    n = rng.randrange(1,9)
    edges = [(rng.randrange(n),rng.randrange(n)) for i in range(rng.randrange(13))]
    order = list(range(len(edges)))
    rng.shuffle(order)
    p = rng.randrange(1+len(edges)//2)
    pairs = list(zip(order[:p],order[p:2*p]))
    s,t = rng.randrange(n),rng.randrange(n)
    rank, path = solve(n,edges,pairs,s,t)
    assert (path is not None) == brute(edges,pairs,s,t)
    if path is not None:
        v = s
        seen = {v}
        for i in path:
            u,w = edges[i]
            assert v in (u,w)
            v = w if v == u else u
            assert v not in seen
            seen.add(v)
        assert v == t and all(not set(pair) <= set(path) for pair in pairs)
# Noncube seed branch: many loop alternatives and one bridge.
edges = [(0,0)]*40 + [(0,1),(1,1)]
rank,path = solve(2,edges,[(i,i+1) for i in range(0,42,2)],0,1)
assert rank == 0 and path == [40]
assert solve(2,edges,[(i,i+1) for i in range(0,42,2)],0,1,optimize=False) == (1,[40])
print("1200 random multigraphs and one noncube seed case passed")
