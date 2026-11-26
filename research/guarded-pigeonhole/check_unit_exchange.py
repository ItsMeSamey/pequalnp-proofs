"""Exact two-switch and singleton audit on K(4,4) with two added edges."""
from collections import Counter
from itertools import combinations, permutations
from mask_lp import compiler

vertices = range(4)
edges = list(combinations(vertices, 2))
old = [(u, v) for u in vertices for v in vertices if u != v] + [(4, 0), (4, 1)]
normals, _, marker, _ = compiler(4, old)
possible = {('old', i): set() for i in range(len(normals))}
for sel in range(2):
    for j in range(2):
        for v in vertices:
            possible.setdefault(('a', j, v), set()).add(int(j == sel))
        for i in range(len(edges)):
            possible.setdefault(('z', j, i), set()).update((0, 1) if j != sel else ())
    for pi in permutations(vertices):
        mask = sum(1 << i for i, (u,v) in enumerate(old[:-2]) if pi[u] == v) | (1 << (12+sel))
        assert (mask & marker).bit_count() % 2 == 1
        for i, normal in enumerate(normals):
            b = (mask >> i) & 1
            possible['old',i].add(b)
            assert b * (1 ^ ((normal & mask).bit_count() % 2) ^ int(i == 12+sel)) == 0
assert all(values == {0,1} for values in possible.values())

def components(F):
    unseen = set(vertices)
    while unseen:
        comp = {next(iter(unseen))}
        while True:
            new = comp | {v for i, e in enumerate(edges) if i not in F and comp.intersection(e) for v in e}
            if new == comp:
                break
            comp = new
        unseen -= comp
        yield comp

def projects(F,d):
    weights = Counter()
    for x in range(1 << len(edges)):
        if all(sum((x >> i) & 1 for i,e in enumerate(edges) if v in e) % 2 == ((v == 0) ^ (v == d))
               for v in vertices):
            weights[x & sum(1 << i for i in F)] += 1
    return weights

views = {}
for s in range(4):
    for F in combinations(range(len(edges)), s):
        giant = max(components(F),key=len)
        assert len(giant) > 2
        options = [projects(F,d) for d in giant]
        assert all(option == options[0] for option in options) and sum(options[0].values()) == 8
        views[F] = options[0]
        fm = sum(1 << i for i in F)
        for v in vertices:
            star = sum(1 << i for i,e in enumerate(edges) if v in e)
            if star & fm == star:
                assert all((x & star).bit_count() % 2 == (v == 0) for x in views[F])
        for i in F:
            rest = tuple(j for j in F if j != i)
            reduced = Counter()
            for x,w in views[F].items():
                reduced[x & ~(1 << i)] += w
            assert reduced == views[rest]
print(f'Both values witnessed on {len(possible)} singleton coordinates; {len(views)} exact edge marginals checked.')
