"""Check the parameter-preserving edge-routing reduction on small DAGs."""
from itertools import combinations, product
from random import Random
from solver import solve


def encode(n, edges, demands):
    k = len(demands)
    rows = [[] for _ in range(n)]
    for j, (u,v) in enumerate(edges):
        options = []
        for i, (s,t) in enumerate(demands):
            literals = [(0, 1)] if u == s else [(1 << (k*f+i),0) for f, (_,w) in enumerate(edges) if w == u]
            options.append((1 << (k*j+i), literals))
        rows[u].append(options)
    targets = [(sum(1 << (k*j+i) for j, (_,v) in enumerate(edges) if v == t), 1)
               for i, (s,t) in enumerate(demands)]
    return [row for row in rows if row], targets


def paths(u, t, edges):
    if u == t:
        yield 0
        return
    for j, (v,w) in enumerate(edges):
        if v == u:
            for mask in paths(w,t,edges):
                yield (1 << j) | mask


def verify(n, edges, demands):
    families = [list(paths(s,t,edges)) for s,t in demands]
    feasible = any(sum(e.bit_count() for e in picked) == sum(
        any(e >> j & 1 for e in picked) for j in range(len(edges))) for picked in product(*families))
    answer = solve(*encode(n,edges,demands))
    assert feasible == (answer is not None)


if __name__ == '__main__':
    rng = Random(17813)
    checked = 0
    for n in range(2,6):
        choices = list(combinations(range(n),2))
        for _ in range(70):
            edges = [e for e in choices if rng.random() < .4]
            demands = [rng.choice(choices) for _ in range(rng.randint(1,3))]
            verify(n,edges,demands)
            checked += 1
    print(checked)
