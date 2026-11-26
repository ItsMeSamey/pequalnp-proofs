"""Check every local equality for the supplied universal forest distributions."""
from ast import literal_eval
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
from functools import cache


@cache
def value(n, edges, colours):
    if any(colours[i] == colours[j] for i, j in edges):
        return Fraction(0)
    options = []
    for perm in permutations(range(n)):
        graph = tuple(sorted(tuple(sorted((perm[i],perm[j]))) for i,j in edges))
        groups = tuple(sorted(tuple(sorted(perm[i] for i,v in enumerate(colours) if v==c))
                              for c in set(colours)))
        options.append((n,graph,groups))
    return TABLE[min(options)]


TABLE = {}
for line in Path(__file__).with_name("colour-sa4-orbits.txt").read_text().splitlines():
    key, number = line.rsplit(" ", 1)
    TABLE[literal_eval(key)] = Fraction(number)
assert len(TABLE)==32 and min(TABLE.values())>=0
assert value(0,(),())==1
tests=0
for n in range(1,5):
    possible = list(combinations(range(n),2))
    for mask in range(1<<len(possible)):
        edges = tuple(e for i,e in enumerate(possible) if mask>>i&1)
        groups = [{i} for i in range(n)]
        for a,b in edges:
            ga,gb = next(g for g in groups if a in g),next(g for g in groups if b in g)
            if ga==gb:
                break
            groups.remove(ga)
            groups.remove(gb)
            groups.append(ga|gb)
        else:
            for omit in range(n):
                small = tuple((a-(a>omit),b-(b>omit)) for a,b in edges if omit not in (a,b))
                for cs in product(range(3),repeat=n-1):
                    assert sum(value(n,edges,cs[:omit]+(c,)+cs[omit:]) for c in range(3))==value(n-1,small,cs)
                    tests+=1
print(f"{tests} exact one-vertex marginal equalities")
