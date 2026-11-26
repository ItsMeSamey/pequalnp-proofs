"""Independent exact cube-union checks with declared-variable core cofactors."""
from itertools import combinations, product
from collections import defaultdict


def merge(u,v):
    if (u[1]^v[1]) & u[0] & v[0]:
        return None
    return (u[0]|v[0],u[1]|v[1])


def poly(cubes):
    entries = {(0,0):1}
    for v in cubes:
        changed = defaultdict(int,entries)
        for u,c in entries.items():
            w = merge(u,v)
            if w is not None:
                changed[w] -= c
        entries = {u:c for u,c in changed.items() if c}
    return entries


def check(n,cubes):
    entries = poly(cubes)
    universe = range(1<<n)
    def evaluate(x):
        return sum(c for (mask,pins),c in entries.items() if x&mask==pins)
    accepted = [not any(x&m==b for m,b in cubes) for x in universe]
    assert all(evaluate(x)==y for x,y in zip(universe,accepted))
    for core in (lambda x:True, lambda x:False, lambda x:x%3!=0):
        assert sum(c*sum(core(x) for x in universe if x&m==b)
                   for (m,b),c in entries.items()) == sum(core(x)*accepted[x] for x in universe)


if __name__=='__main__':
    cases = 0
    for n,limit in ((2,9),(3,3)):
        cubes = [(m,b) for m,b in product(range(1<<n),repeat=2) if b&m==b]
        for k in range(limit+1):
            for seq in combinations(cubes,k):
                check(n,seq)
                cases += 1
    for d in range(4):
        # Three signed payloads with incompatible two-bit tags.
        size = 5
        cubes = []
        for tag,payload in enumerate((0,13,31)):
            for omit in combinations(range(size),d):
                m = ((1<<size)-1)^sum(1<<i for i in omit)
                cubes.append((m*4+3,(payload&m)*4+tag))
        check(7,cubes)
        supports = {frozenset(i for i,(m,b) in enumerate(cubes) if x&m==b) for x in range(128)}
        assert all(frozenset([i]) in supports for i in range(len(cubes)))
    print(cases,'unstructured CNFs and four signed tagged omission families passed')
