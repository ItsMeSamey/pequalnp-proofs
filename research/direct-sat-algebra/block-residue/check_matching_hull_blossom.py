"""Independent small-graph exhaustive oracles for matching hull and cardinality."""
from functools import lru_cache
from itertools import combinations
from random import Random

from general_blossom import maximum_cardinality_matching
from matching_hull import matching_hull


def oracle(n, edges):
    incident = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        assert u != v
        incident[u].append((v, i))
        incident[v].append((u, i))

    @lru_cache(None)
    def maximum(remaining):
        if not remaining:
            return 0
        u = (remaining & -remaining).bit_length() - 1
        rest = remaining ^ (1 << u)
        best = maximum(rest)
        for v, _ in incident[u]:
            if rest & (1 << v):
                best = max(best, 1 + maximum(rest ^ (1 << v)))
        return best

    def perfect(remaining, picked):
        if not remaining:
            yield picked | (1 << len(edges))
            return
        u = (remaining & -remaining).bit_length() - 1
        rest = remaining ^ (1 << u)
        for v, i in incident[u]:
            if rest & (1 << v):
                yield from perfect(rest ^ (1 << v), picked | (1 << i))

    all_vertices = (1 << n) - 1
    return maximum(all_vertices), list(perfect(all_vertices, 0))


def canonical(rows):
    pivots = {}
    for row in rows:
        for k in sorted(pivots, reverse=True):
            if row & (1 << k):
                row ^= pivots[k]
        if row:
            k = row.bit_length() - 1
            for old in pivots:
                if pivots[old] & (1 << k):
                    pivots[old] ^= row
            pivots[k] = row
    return tuple(pivots[k] for k in sorted(pivots))


def check(name, n, edges):
    cardinality, perfect = oracle(n, edges)
    matching = list(maximum_cardinality_matching(range(n), list(edges)))
    valid = {frozenset(edge) for edge in edges}
    used = set()
    for a, b in matching:
        assert a != b and frozenset((a, b)) in valid, (name, matching)
        assert a not in used and b not in used, (name, matching)
        used.update((a, b))
    assert len(matching) == cardinality, (name, matching, cardinality)
    basis = list(matching_hull(range(n), list(edges)))
    assert all(isinstance(x, int) and 0 < x < 1 << (len(edges) + 1)
               for x in basis), (name, basis)
    reduced = canonical(basis)
    assert len(reduced) == len(basis), (name, "dependent basis")
    assert reduced == canonical(perfect), (name, edges, basis, perfect)


def fixtures():
    k4 = list(combinations(range(4), 2))
    cube = [(i, i ^ d) for i in range(8) for d in (1, 2, 4) if i < i ^ d]
    petersen = ([(i, (i + 1) % 5) for i in range(5)]
                + [(i, 5 + i) for i in range(5)]
                + [(5 + i, 5 + (i + 2) % 5) for i in range(5)])
    yield "empty", 0, []
    yield "isolates", 4, []
    yield "K4 brick", 4, k4
    yield "cube", 8, cube
    yield "upper triangular unique PM", 6, [(i, 3+j) for i in range(3)
                                            for j in range(i, 3)]
    mobius = [(i, (i + 1) % 12) for i in range(12)] + [(i, i + 6) for i in range(6)]
    # Independently check bicriticality in the oracle before using this brick.
    for a, b in combinations(range(12), 2):
        label = {u: i for i, u in enumerate(v for v in range(12) if v not in (a, b))}
        sub = [(label[u], label[v]) for u, v in mobius if u in label and v in label]
        assert oracle(10, sub)[0] == 5
        reached = {0}
        for _ in range(9):
            reached.update(v for u, v in sub if u in reached)
            reached.update(u for u, v in sub if v in reached)
        assert len(reached) == 10
    yield "12-vertex Mobius ladder brick", 12, mobius
    yield "Petersen", 10, petersen
    yield "Petersen replicated edge", 10, petersen + [petersen[0]]
    yield "unusable bridge and replicated allowed edge", 4, [
        (0, 1), (1, 2), (2, 3), (1, 0)]
    yield "disconnected feasible", 8, k4 + [(4, 5), (4, 5), (6, 7)]
    yield "two odd components", 6, [(0, 1), (1, 2), (2, 0),
                                    (3, 4), (4, 5), (5, 3)]

    # Splice K4 bricks at two cube vertices of the same parity. Each new
    # triangle sends an odd positive number of matching edges to the cube.
    # The remaining cube bipartition forces their total to be exactly two.
    removed = (0, 3)
    labels = {v: j for j, v in enumerate(i for i in range(8) if i not in removed)}
    spliced = [(labels[a], labels[b]) for a, b in cube if a in labels and b in labels]
    for j, v in enumerate(removed):
        triangle = list(range(6 + 3 * j, 9 + 3 * j))
        spliced.extend(combinations(triangle, 2))
        spliced.extend((port, labels[v ^ d]) for port, d in zip(triangle, (1, 2, 4)))
    yield "two K4 bricks spliced into cube", 12, spliced


def main():
    cases = 0
    for name, n, edges in fixtures():
        check(name, n, edges)
        cases += 1
    for n in range(5):
        possible = list(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = [e for j, e in enumerate(possible) if mask & (1 << j)]
            check(("all simple", n, mask), n, edges)
            cases += 1
    rng = Random(734019)
    for n in range(2, 10):
        for trial in range(12):
            edges = [e for e in combinations(range(n), 2) if rng.randrange(5) < 2]
            if edges and trial % 2 == 0:
                edges.append(rng.choice(edges))
            rng.shuffle(edges)
            check(("random", n, trial), n, edges)
            cases += 1
    print("matching hull and blossom oracle cases", cases)


if __name__ == "__main__":
    main()
