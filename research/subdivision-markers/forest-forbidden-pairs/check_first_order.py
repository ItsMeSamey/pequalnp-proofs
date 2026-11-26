"""Test parsimonious occurrence cloning and its resulting physical bandwidth certificate."""
from collections import Counter
from itertools import product
from random import Random
from sys import argv
import json

from check_first_true import build


def clone_formula(rows, n):
    owner = []
    occurrence_ids = [[] for _ in range(n)]
    new_rows = []
    for row in rows:
        cloned = []
        for v, neg in row:
            idx = len(owner)
            owner.append(v)
            occurrence_ids[v].append(idx)
            cloned.append((idx, neg))
        new_rows.append(cloned)
    for v, ids in enumerate(occurrence_ids):
        if not ids:
            owner.append(v)
        elif len(ids) >= 2:
            for i, src in enumerate(ids):
                dst = ids[(i+1) % len(ids)]
                new_rows.append([(src,1),(dst,0),(dst,0)])
    return new_rows, owner


def satisfies(formula, x):
    return all(any(x[v] ^ neg for v,neg in row) for row in formula)


def check(rows, n, inspect=False):
    cloned, owner = clone_formula(rows,n)
    occ = Counter(v for row in cloned for v,neg in row)
    assert max(occ.values(),default=0) <= 4
    lhs = Counter()
    for y in product(range(2), repeat=len(owner)):
        if not satisfies(cloned,y):
            continue
        x = [None]*n
        for i,v in enumerate(owner):
            assert x[v] in (None,y[i])
            x[v] = y[i]
        lhs[tuple(x)] += 1
    for x in product(range(2),repeat=n):
        assert lhs[x] == int(satisfies(rows,x))

    graph,edges,pairs,truth,order = build(cloned,len(owner))
    assert len(order) == len(set(order)) == len(graph)
    positions = {v:i for i,v in enumerate(order)}
    span = max(abs(positions[a]-positions[b]) for a,b in edges)
    assert span <= 51
    assert len(set(e for p in pairs for e in p)) == 2*len(pairs) == 12*len(cloned)
    if inspect:
        return dict(source=rows,clone_to_original=owner,cloned_formula=cloned,
                    graph_edges=edges,forbidden_edge_id_pairs=pairs,vertex_order=order,max_span=span)
    return len(owner),span


if __name__ == '__main__':
    example = [[(0,0),(0,1),(0,0)],[(0,0),(0,0),(0,1)],[(0,1),(0,0),(0,0)]]
    if '--example' in argv:
        print(json.dumps(check(example,2,True)))
    else:
        cases = [(example,2),([],0),([],2),([[(0,0)]*3,[(0,1)]*3],2)]
        rng = Random(9712)
        for i in range(80):
            n = rng.randrange(1,4)
            rows = [[(rng.randrange(n),rng.randrange(2)) for _ in range(3)]
                    for _ in range(1+i%3)]
            cases.append((rows,n))
        results = [check(rows,n) for rows,n in cases]
        print(len(results),'source formulas;',sum(2**k for k, _ in results),
              'clone assignments;',max(span for _,span in results),'largest observed span')
