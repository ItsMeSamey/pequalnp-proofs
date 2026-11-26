"""Exact code-space checks for the three-shore connector and rooted K4."""
from itertools import product
from random import Random


def graph_codes(n, edges):
    cuts = {sum(int(((colors >> u) ^ (colors >> v)) & 1) << i
                for i, (u, v) in enumerate(edges)) for colors in range(1 << n)}
    rows = [sum((((u == v) ^ (w == v)) << e) for e, (u, w) in enumerate(edges))
            for v in range(n)]
    cycles = {x for x in range(1 << len(edges))
              if all((x & row).bit_count() % 2 == 0 for row in rows)}
    return cuts, cycles


def middle_codes():
    triangle = [(1, 2), (2, 0), (0, 1)]
    cuts, cycles = graph_codes(3, triangle * 3)
    def encode(u, v, w):
        return u | v << 3 | w << 6
    primal = {(u, v, w) for u, v, w in product(range(8), repeat=3)
              if encode(u, v, w) in cycles}
    dual = {(u, v, w) for u, v, w in product(range(8), repeat=3)
            if encode(u, v, w) in cuts}
    assert primal == {(u, v, w) for u, v, w in product(range(8), repeat=3)
                      if u ^ v ^ w in (0, 7)}
    assert dual == {(s, s, s) for s in (0, 3, 5, 6)}
    kcuts, kcycles = graph_codes(4, triangle + [(i, 3) for i in range(3)])
    disjoint = {(x & 7, y & 7) for x in kcycles for y in kcuts if not x & y & 56}
    assert disjoint == {(t, s) for t in range(8) for s in (0, 3, 5, 6)
                        if (t & s).bit_count() % 2 == 0}
    return primal, dual


def glue(a, b, na, nb, allowed):
    by_trace = []
    for code, k in ((a, na), (b, nb)):
        groups = [set() for _ in range(8)]
        for x in code:
            groups[x >> k].add(x & ((1 << k) - 1))
        by_trace.append(groups)
    return {x | y << na | w << (na + nb) for u, v, w in allowed
            for x in by_trace[0][u] for y in by_trace[1][v]}


def main():
    primal, dual = middle_codes()
    rng = Random(860)
    for _ in range(96):
        sizes = [rng.randint(1, 4) for _ in range(2)]
        shores, ports = [], []
        for n in sizes:
            edges = [(rng.randrange(i), i) for i in range(1, n)]
            for _ in range(rng.randrange(3)):
                edges.append((rng.randrange(n), rng.randrange(n)))
            shores.append(edges)
            ports.append([rng.randrange(n) for _ in range(3)])
        nl, nr = sizes
        a, b = shores
        l, r = ports
        global_edges = a + [(u+nl, v+nl) for u, v in b] + list(zip(l, [v+nl for v in r]))
        cuts, flows = graph_codes(nl+nr, global_edges)
        ac, af = graph_codes(nl+1, a + [(u, nl) for u in l])
        bc, bf = graph_codes(nr+1, b + [(u, nr) for u in r])
        assert cuts == glue(ac, bc, len(a), len(b), primal)
        assert flows == glue(af, bf, len(a), len(b), dual)
    print('96 one-cut code identities, 512 connector triples, and all 32 K4 boundary pairs passed.')


if __name__ == '__main__':
    main()
