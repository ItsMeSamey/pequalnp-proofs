"""Rooted forest-reference solver for disjoint triple and optional swap sockets."""
from itertools import product
from random import Random

from attainable_forest_reference import augment
from strict_forest_reference import circles, colored_path, physical, split_chords, swap


def realise(p, triples, transpositions, mask):
    first = physical(p, triples, mask[:len(triples)])
    return swap(first, [e for e, on in zip(transpositions, mask[len(triples):]) if on])


def solve(p, triples, transpositions, s, t, baseline=None):
    """Return (recognized, mask), with triples first, then optional transpositions."""
    n = len(triples)
    if baseline is None:
        baseline = [False] * n
    sockets = [v for g in [*triples, *transpositions] for v in g]
    if (sorted(p) != list(range(len(p))) or len(sockets) != len(set(sockets))
            or any(not 0 <= v < len(p) for v in [*sockets, s, t])
            or any(len(g) != 3 for g in triples)
            or any(len(g) != 2 for g in transpositions) or len(baseline) != n):
        raise ValueError("Expected a permutation, disjoint native sockets, valid marks and a triple baseline.")
    reference = physical(p, triples, baseline)
    chords = split_chords(reference, triples)
    if chords is None:
        return False, None
    opposite = swap(reference, chords)
    orbits = circles(opposite)
    label = {v: i for i, orbit in enumerate(orbits) for v in orbit}
    edges = []
    for color, triple in enumerate(triples):
        for on in (False, True):
            u, v = [x for j, x in enumerate(triple)
                    if opposite[x] != p[triple[(j + int(on)) % 3]]]
            edges.append((label[u], label[v], color, on))
    for j, (u, v) in enumerate(transpositions):
        edges.append((label[u], label[v], n + j, True))

    path = colored_path(edges, label[s], label[t])
    if path is None:
        return True, None
    index = {(color, on): j for j, (_, _, color, on) in enumerate(edges)}
    selected = {index[key] for key in path}
    for j in range(len(transpositions)):
        private = len(orbits) + 2*j
        edges.append((private, private + 1, n + j, False))
    while len(selected) < n + len(transpositions):
        enlarged = augment(edges, selected)
        assert enlarged is not None
        selected = enlarged
    mask = [False] * (n + len(transpositions))
    for j in selected:
        _, _, color, on = edges[j]
        mask[color] = on
    assert any(s in w and t in w for w in circles(realise(p, triples, transpositions, mask)))
    return True, mask


if __name__ == "__main__":
    rng = Random(93681)
    cases = recognized = yes = no = 0
    for n, k in product(range(4), repeat=2):
        for _ in range(35):
            size = 3*n + 2*k + 2
            p = list(range(size))
            rng.shuffle(p)
            slots = rng.sample(range(size), 3*n + 2*k)
            triples = [tuple(slots[3*i:3*i+3]) for i in range(n)]
            opts = [tuple(slots[3*n+2*i:3*n+2*i+2]) for i in range(k)]
            baseline = [rng.choice([False, True]) for i in range(n)]
            def trace(bits):
                q = list(p)
                for gate, on in zip(triples + opts, bits):
                    if on:
                        for j, v in enumerate(gate):
                            q[v] = p[gate[(j+1) % len(gate)]]
                return circles(q)
            all_orbits = [trace(bits) for bits in product((False, True), repeat=n+k)]
            for s, t in [rng.sample(range(size), 2), (0, 0)]:
                cases += 1
                ok, mask = solve(p, triples, opts, s, t, baseline)
                if ok:
                    recognized += 1
                    expected = any(any(s in w and t in w for w in z) for z in all_orbits)
                    assert expected == (mask is not None)
                    if expected:
                        yes += 1
                        assert len(mask) == n+k and any(s in w and t in w for w in trace(mask))
                    else:
                        no += 1
    print(f"{cases} cases, {recognized} recognized, {yes} YES and {no} NO")
