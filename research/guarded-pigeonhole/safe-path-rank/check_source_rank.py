"""Compare SAT source, safe-path verdict and minimum cover by direct small enumeration."""
from random import Random
from safe_path_rank import solve

def compile_formula(n, formula):
    blocks = n + len(formula)
    next_vertex = blocks+1
    edges, occurrence_edge, pairs = [], {}, []
    for variable in range(n):
        for bit in (0,1):
            occ = [(j,k) for j,clause in enumerate(formula) for k,(v,b) in enumerate(clause)
                   if v == variable and b == bit]
            prev = variable
            for idx, occurrence in enumerate(occ or [None]):
                if idx+1 >= len(occ):
                    w = variable+1
                else:
                    w = next_vertex
                    next_vertex += 1
                if occurrence is not None:
                    occurrence_edge[occurrence] = len(edges)
                edges.append((prev,w))
                prev = w
    for j,clause in enumerate(formula):
        for k,_ in enumerate(clause):
            pairs.append((occurrence_edge[j,k],len(edges)))
            edges.append((n+j,n+j+1))
    return next_vertex, edges, pairs, 0, blocks

def cover(n, formula):
    deg = [sum(v==i for c in formula for v,b in c) for i in range(n)]
    return min(sum(max(0,deg[i]-1) for i in range(n) if chosen>>i&1)
               +sum(any(not (chosen>>v & 1) for v,b in c) for c in formula)
               for chosen in range(1<<n))

rng = Random(80129)
for _ in range(180):
    n = rng.randrange(1,5)
    formula = [[(rng.randrange(n),rng.randrange(2)) for k in range(rng.randrange(1,4))]
               for j in range(rng.randrange(1,6))]
    expected = any(all(any((word>>v & 1) != b for v,b in c) for c in formula)
                   for word in range(1<<n))
    graph = compile_formula(n,formula)
    rank,path = solve(*graph)
    assert rank == cover(n,formula) and (path is not None) == expected
    assert solve(*graph,optimize=False)[0] >= len(formula)
print("180 serial SAT sources passed rank, vertex-cover, and truth-table comparisons")
