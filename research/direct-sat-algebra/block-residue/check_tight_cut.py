"""Independent exhaustive tight-shore oracle on small matching-covered graphs."""
from itertools import combinations
from tight_cut import tight_shore


def perfect_matchings(vertices, edges):
    if not vertices:
        yield ()
        return
    x = min(vertices)
    for e, (u, v) in enumerate(edges):
        if x in (u, v) and u in vertices and v in vertices:
            for rest in perfect_matchings(vertices - {u, v}, edges):
                yield (e,) + rest


def check(n, edges):
    vertices = set(range(n))
    matchings = list(perfect_matchings(vertices, edges))
    assert set(range(len(edges))) == set().union(*(set(m) for m in matchings))
    def tight(shore):
        return all(sum((edges[e][0] in shore) != (edges[e][1] in shore)
                       for e in matching) == 1 for matching in matchings)
    exists = any(tight(set(shore)) for k in range(3, n-2, 2)
                 for shore in combinations(vertices, k))
    found = tight_shore(n, edges)
    assert (found is not None) == exists
    if found is not None:
        assert 3 <= len(found) <= n-3 and tight(found)


def main():
    k33 = [(u, v) for u in range(3) for v in range(3, 6)]
    barrier = [(u, v) for u in (0, 1) for v in (2, 3, 4)]
    barrier += [(2, 5), (3, 6), (4, 7), (5, 6), (6, 7), (7, 5)]
    split = list(combinations([0, 1, 2, 3], 2))
    split += [e for e in combinations([0, 1, 4, 5], 2) if e != (0, 1)]
    graphs = [(6, k33), (6, [(i, (i+1) % 6) for i in range(6)]),
              (8, barrier), (6, split), (6, list(combinations(range(6), 2)))]
    for n, edges in graphs:
        check(n, edges)
        check(n, edges + [edges[0], edges[-1]])
    print("10 connected matching-covered tight-cut oracle fixtures")


if __name__ == "__main__":
    main()
