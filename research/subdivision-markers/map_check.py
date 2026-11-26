"""Check exact surjectivity of the bounded-degree parametrization with defect screening."""
from itertools import combinations
from random import Random


def basis_rank(vectors):
    pivots = {}
    for v in vectors:
        while v:
            pivot = v.bit_length()
            if pivot not in pivots:
                pivots[pivot] = v
                break
            v ^= pivots[pivot]
    return len(pivots)


def check(n, edges):
    adjacency = [0] * n
    incidence = [0] * n
    for i, (u, v) in enumerate(edges):
        adjacency[u] |= 1 << v
        adjacency[v] |= 1 << u
        incidence[u] |= 1 << i
        incidence[v] |= 1 << i
    universe = range(1 << n)
    iso_seeds = [sum(1 << v for v in range(n) if y >> v & 1 and not (y & adjacency[v]))
                 for y in universe]
    direct = {s for s in universe if all(not ((s & adjacency[v]).bit_count() % 2)
                                        for v in range(n) if s >> v & 1)}
    obtained = set()
    degree = [x.bit_count() for x in incidence]
    bad = [i for i, (u, v) in enumerate(edges) if min(degree[u], degree[v]) >= 3]
    values = {i: 0 for i in bad}
    cycle_count = 0
    for z in range(1 << len(edges)):
        if any((z & incident).bit_count() % 2 for incident in incidence):
            continue
        active = sum(1 << v for v in range(n) if z & incidence[v])
        defects = 0
        for i in bad:
            u, v = edges[i]
            du = incidence[u] ^ (1 << i)
            dv = incidence[v] ^ (1 << i)
            actual = not (z >> i & 1) and active >> u & 1 and active >> v & 1
            local = not (z >> i & 1) and bool(z & (du ^ (du & -du))) and bool(z & (dv ^ (dv & -dv)))
            assert bool(actual) == local
            if actual:
                defects |= 1 << i
                values[i] |= 1 << cycle_count
        cycle_count += 1
        if defects:
            continue
        eligible = sum(1 << v for v in range(n) if not (adjacency[v] & active))
        obtained.update(active | (eligible & independent) for independent in iso_seeds)
    assert obtained == direct
    return basis_rank(values.values())


if __name__ == '__main__':
    graphs = 0
    ranks = set()
    for n in range(1, 6):
        complete = list(combinations(range(n), 2))
        for mask in range(1 << len(complete)):
            ranks.add(check(n, [e for i, e in enumerate(complete) if mask >> i & 1]))
            graphs += 1
    rng = Random(94837)
    for _ in range(140):
        n = rng.randint(6, 11)
        edges = list(combinations(range(n), 2))
        rng.shuffle(edges)
        ranks.add(check(n, edges[:rng.randrange(2, 14)]))
        graphs += 1
    print(graphs, sorted(ranks))
