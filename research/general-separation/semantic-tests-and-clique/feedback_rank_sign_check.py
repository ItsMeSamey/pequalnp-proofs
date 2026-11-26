"""Signed Bellman counts with unit cost on departure from a feedback vertex."""
from itertools import product
from random import Random

def counts(rows, feedback):
    n = len(rows)
    inf = len(feedback)+1
    def simple(u, seen):
        if u == n:
            return 0
        if u in seen:
            return inf
        return min([inf]+[min(inf,(u in feedback)+simple(v,seen|{u})) for v in rows[u]])
    canonical = tuple(simple(u,set()) for u in range(n))
    survivors = []
    for vector in product(range(inf+1),repeat=n):
        ranks = vector+(0,)
        rowsums = [[min(inf,(u in feedback)+ranks[v]) for v in row] for u,row in enumerate(rows)]
        if any(any(vector[u]>c for c in amounts) for u,amounts in enumerate(rowsums)):
            continue
        free = [u for u in range(n) if vector[u]<inf and vector[u] not in rowsums[u]]
        signed = sum((-1)**sum(flags) for flags in product((0,1),repeat=len(free)))
        if signed:
            assert signed==1
            survivors.append(vector)
    return canonical,survivors

def feedback_valid(rows, f):
    n = len(rows)
    def cycle(u,path):
        return u!=n and u not in f and (u in path or any(cycle(v,path|{u}) for v in rows[u]))
    return not any(cycle(u,set()) for u in range(n))

cases = 0
for masks in product(range(8), repeat=2):
    rows = [[v for v in range(3) if m>>v&1] for m in masks]
    for mask in range(4):
        f = {u for u in range(2) if mask>>u&1}
        if feedback_valid(rows,f):
            canonical,survivors = counts(rows,f)
            assert survivors==[canonical]
            cases += 1
rng = Random(799)
for _ in range(350):
    n = 3
    branches = [[[v for v in range(n+1) if rng.randrange(3)==0] for _ in range(2)] for u in range(n)]
    union = [set(a)|set(b) for a,b in branches]
    f = {u for u in range(n) if rng.randrange(2)}
    if not feedback_valid(union,f):
        continue
    labels = [rng.randrange(2) for u in range(n)]
    for x in product(range(2),repeat=2):
        rows = [row[x[label]] for row,label in zip(branches,labels)]
        canonical,survivors=counts(rows,f)
        assert survivors==[canonical]
        cases += 1
assert counts([[0]],set())==((1,),[(0,),(1,)])
print(cases,'valid cases passed; missed self-loop has false finite survivor')
