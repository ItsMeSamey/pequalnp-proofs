"""Verify the induced-forest-type level-five obstruction using integer arithmetic."""
from collections import Counter
from functools import cache
from itertools import permutations
from pathlib import Path
import json


@cache
def orbit(n, edges, assignment):
    candidates = []
    for p in permutations(range(n)):
        graph = tuple(sorted(tuple(sorted((p[u], p[v]))) for u,v in edges))
        cells = tuple(sorted(tuple(sorted(p[i] for i,x in enumerate(assignment) if x==c))
                             for c in set(assignment)))
        candidates.append((n,graph,cells))
    return min(candidates)


def row(n, edges, omitted, colours):
    assert 1 <= n <= 5 and 0 <= omitted < n and len(colours)==n-1
    assert all(c in range(3) for c in colours)
    groups = [{i} for i in range(n)]
    for u,v in edges:
        a,b = next(g for g in groups if u in g), next(g for g in groups if v in g)
        assert a != b
        groups.remove(a)
        groups.remove(b)
        groups.append(a|b)
    short = tuple((u-(u>omitted),v-(v>omitted)) for u,v in edges if omitted not in (u,v))
    assert all(colours[u]!=colours[v] for u,v in short)
    result = Counter({orbit(n-1,short,colours):-1})
    for c in range(3):
        full=colours[:omitted]+(c,)+colours[omitted:]
        if all(full[u]!=full[v] for u,v in edges):
            result[orbit(n,edges,full)]+=1
    return result


if __name__ == '__main__':
    certificate=json.loads(Path(__file__).with_name("colour-forest-sa5-obstruction.json").read_text())
    total=Counter()
    for multiplier,n,edges,v,colours in certificate:
        for k,a in row(n,tuple(map(tuple,edges)),v,tuple(colours)).items():
            total[k]+=multiplier*a
    total={k:v for k,v in total.items() if v}
    assert total=={(0,(),()):1}
    print(f"{len(certificate)} integer-weighted marginal identities sum to empty mass = 0")
