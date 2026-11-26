"""Compare primal cut traces and projected dual-cycle traces for every subset."""
from random import Random


def span(values):
    out = {0}
    for v in values:
        out |= {x ^ v for x in out}
    return out


def incidence(n, edges):
    rows = [0] * n
    for i, (a, b) in enumerate(edges):
        rows[a] ^= 1 << i
        rows[b] ^= 1 << i
    return rows


def dual_graph(n, edges, rng=None):
    rotations = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        rotations[a].append(2 * i)
        rotations[b].append(2 * i + 1)
    successor = {}
    for cyclic in rotations:
        if rng is not None:
            rng.shuffle(cyclic)
        for i, half in enumerate(cyclic):
            successor[half] = cyclic[(i + 1) % len(cyclic)]
    faces, assigned = 0, {}
    for half in range(2 * len(edges)):
        if half in assigned:
            continue
        step = half
        while step not in assigned:
            assigned[step] = faces
            step = successor[step ^ 1]
        assert step == half
        faces += 1
    return faces, [(assigned[2*i], assigned[2*i+1]) for i in range(len(edges))]


def check(n, edges, rng, rotate=True):
    m = len(edges)
    full = range(1 << m)
    primal = incidence(n, edges)
    faces, dual = dual_graph(n, edges, rng if rotate else None)
    dual_rows = incidence(faces, dual)
    euler_genus = 2 - n + m - faces
    assert euler_genus >= 0 and euler_genus % 2 == 0
    cuts = span(primal)
    cycles = {s for s in full if all((s & row).bit_count() % 2 == 0 for row in dual_rows)}
    assert cuts <= cycles
    check_rows = span(dual_rows)
    auxiliary = []
    for s in full:
        if s in check_rows or any((s & v).bit_count() % 2 for v in primal):
            continue
        auxiliary.append(s)
        check_rows |= {x ^ s for x in check_rows}
    assert len(auxiliary) == euler_genus
    r = rng.randrange(1, 5)
    edge_labels = [rng.randrange(1 << r) for _ in edges]
    scores = [0] * (1 << m)
    for s in range(1, 1 << m):
        bit = s & -s
        scores[s] = scores[s ^ bit] ^ edge_labels[bit.bit_length() - 1]
    augmented = {s: scores[s] | (sum(((s & v).bit_count() % 2) << i
                                      for i, v in enumerate(auxiliary)) << r)
                 for s in cycles}
    for chosen in full:
        expected = {scores[s] for s in cuts if not (s & ~chosen)}
        augmented_trace = {score for s, score in augmented.items() if not (s & ~chosen)}
        assert {v for v in augmented_trace if v < 1 << r} == expected
    return euler_genus, len(full)


if __name__ == "__main__":
    rng = Random(6781)
    genus, tested = check(6, [(a, b) for a in range(3) for b in range(3, 6)], rng, False)
    assert genus == 2
    genera = {genus}
    for _ in range(100):
        n = rng.randrange(1, 7)
        edges = [(v, rng.randrange(v)) for v in range(1, n)]
        edges += [(rng.randrange(n), rng.randrange(n)) for _ in range(rng.randrange(1, 10-len(edges)))]
        g, count = check(n, edges, rng)
        genera.add(g)
        tested += count
    print(f"101 cellular embeddings, Euler genera {sorted(genera)}, {tested} edge-subset traces matched")
