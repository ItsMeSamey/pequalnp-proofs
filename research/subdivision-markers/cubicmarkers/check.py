"""Exhaustive small-graph cross-check; enumerate parity-factor supports directly."""
import itertools


def connected(s, nb):
    seen = s & -s
    while True:
        expanded = seen
        for i,adj in enumerate(nb):
            if seen >> i & 1:
                expanded |= s & adj
        if expanded == seen:
            return seen == s
        seen = expanded

def check(g):
    n = len(g)
    nb = [sum(1 << j for j in g[i]) for i in range(n)]
    sets = range(1 << n)
    even = [s for s in sets if all(not(s >> i & 1) or (nb[i] & s).bit_count() % 2 == 0 for i in range(n))]
    cycles = [s for s in even if all(not(s >> i & 1) or (nb[i] & s).bit_count() == 2 for i in range(n))]
    onecycle = [s for s in cycles if s and connected(s,nb)]
    degree2 = sum(1 << i for i in range(n) if len(g[i]) == 2)
    tests = 0
    for a,b in itertools.combinations(range(n), 2):
        pins = (1 << a) | (1 << b)
        near = pins | nb[a] | nb[b]
        feasible = [s for s in even if s & pins == pins]
        for w in sets:
            def par(s):
                return (s & w).bit_count() % 2
            actual = set(map(par, feasible))
            if b in g[a]:
                if w & ~degree2:
                    continue
                predicted = set()
                for s in onecycle:
                    if s & pins != pins:
                        continue
                    predicted.add(par(s))
                    if any(w >> i & 1 and not s >> i & 1 and not nb[i] & s for i in range(n)):
                        predicted.add(par(s)^1)
            elif w & ~near:
                predicted = {0,1}
            else:
                predicted = set()
                for iso in sets:
                    if iso & ~near or any(iso >> i & 1 and nb[i] & iso for i in range(n)):
                        continue
                    forbidden = iso
                    for i in range(n):
                        if iso >> i & 1:
                            forbidden |= nb[i]
                    for s in cycles:
                        if not s & forbidden and (s | iso) & pins == pins:
                            predicted.add(par(s | iso))
            assert actual == predicted
            tests += 1
    return tests

if __name__ == '__main__':
    count = tests = 0
    for n in range(2, 6):
        edges = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(edges)):
            g = [[] for _ in range(n)]
            for j,(a,b) in enumerate(edges):
                if mask >> j & 1:
                    g[a].append(b)
                    g[b].append(a)
            if any(len(row) > 3 for row in g) or any(min(len(g[a]),len(g[b])) > 2 for a in range(n) for b in g[a]):
                continue
            count += 1
            tests += check(g)
    print(count, tests)
