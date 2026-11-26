"""Check minimal-carrier trace ranks and two lifted complete-graph examples."""
from itertools import combinations
from random import Random


def rank(vectors):
    pivots = {}
    for x in vectors:
        while x and x.bit_length() in pivots:
            x ^= pivots[x.bit_length()]
        if x:
            pivots[x.bit_length()] = x
    return len(pivots)


def span(vectors):
    found = {0}
    for x in vectors:
        found |= {y ^ x for y in found}
    return frozenset(found)


def subgraph_traces(edges, d):
    mask = (1 << d) - 1
    catalog = []
    for chosen in range(1 << len(edges)):
        lifted = [edge for i, edge in enumerate(edges) if chosen >> i & 1]
        actual = frozenset(x for x in span(lifted) if x <= mask)
        cycle_rank = len(lifted) - rank(x >> d for x in lifted)
        catalog.append((actual, cycle_rank))
    return catalog


def check_carriers():
    rng = Random(2026)
    minimal = 0
    for _ in range(250):
        n, d = rng.randint(1, 6), rng.randint(1, 4)
        edges = []
        for _ in range(rng.randint(0, 8)):
            i, j = rng.randrange(n), rng.randrange(n)
            edges.append((((1 << i) ^ (1 << j)) << d) | rng.randrange(1 << d))
        catalog = subgraph_traces(edges, d)
        for chosen, (trace, beta) in enumerate(catalog):
            if any(chosen >> i & 1 and catalog[chosen ^ (1 << i)][0] == trace
                   for i in range(len(edges))):
                continue
            assert len(trace) == 1 << beta
            minimal += 1
    return minimal


def complete(n, yes):
    pairs = list(combinations(range(n), 2))
    special = [(0, 1), (0, 2), (0, 3), (0, 4)] if yes else [(0, 1), (1, 2), (0, 2), (0, 3)]
    return [(i, j, 1 << special.index((i, j)) if (i, j) in special else 0) for i, j in pairs]


def check_complete():
    for n in range(7, 11):
        for yes in (False, True):
            edges = complete(n, yes)
            packed = [(((1 << i) ^ (1 << j)) << 4) | s for i, j, s in edges]
            assert rank(packed) - rank(v >> 4 for v in packed) == 4
            witnesses = []
            for coloring in range(1 << n):
                allowed = [v for (i, j, s), v in zip(edges, packed)
                           if ((coloring >> i) ^ (coloring >> j) ^ ((s & 9).bit_count())) & 1 == 0]
                if rank(allowed) == rank([*allowed, 15]):
                    witnesses.append(coloring)
            assert bool(witnesses) == yes


if __name__ == "__main__":
    minimal = check_carriers()
    check_complete()
    print(f"Verified {minimal} minimal carriers in 250 labelled multigraphs and 8 complete-graph instances.")
