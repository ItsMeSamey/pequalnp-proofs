"""Bounded tests for the twin-gadget and bipartite parity identities."""
from itertools import combinations, product


def count_even(n, edges, pins=0):
    neighbors = [0] * n
    for u, v in edges:
        neighbors[u] |= 1 << v
        neighbors[v] |= 1 << u
    count = 0
    for x in range(1 << n):
        if (x & pins) != pins:
            continue
        if all(not (x >> i & 1) or (x & row).bit_count() % 2 == 0
               for i, row in enumerate(neighbors)):
            count += 1
    return count


def gadget(n, source):
    edges = []
    for u, v in source:
        for _ in range(2):
            a, b, d = range(n, n + 3)
            n += 3
            edges.extend([(a, b), (a, d), (u, b), (v, b), (v, a)])
    return n, edges


def cover(n, edges):
    return [(a, b + n) for u, v in edges for a, b in ((u, v), (v, u))]


def test():
    local = []
    for u, v in product((0, 1), repeat=2):
        local.append(sum(1 for a, b, d in product((0, 1), repeat=3)
                         if (not a or (b + d + v) % 2 == 0)
                         and (not b or (a + u + v) % 2 == 0)
                         and (not d or a == 0)))
    assert [x % 2 for x in local] == [1, 1, 1, 0]
    cases = 0
    for n in range(1, 5):
        for size in range(min(2, n * (n - 1) // 2) + 1):
            for source in combinations(combinations(range(n), 2), size):
                independent = sum(all(not (x >> u & x >> v & 1)
                                      for u, v in source) for x in range(1 << n))
                m, edges = gadget(n, source)
                assert count_even(m, edges) % 2 == independent % 2
                cases += 1
    double_cases = 0
    for n in range(1, 5):
        all_edges = list(combinations(range(n), 2))
        for mask in range(1 << len(all_edges)):
            edges = [e for i, e in enumerate(all_edges) if mask >> i & 1]
            assert count_even(n, edges) % 2 == count_even(2*n, cover(n, edges)) % 2
            double_cases += 1
    m, edges = gadget(2, [(0, 1)])
    assert count_even(2*m, cover(m, edges)) % 2 == 1
    # This fixed star attachment joins all components by meeting every left vertex.
    # The test example has no isolated right vertex and the forced center is zero.
    k = 6
    pinned_edges = cover(3, [(0, 1), (1, 2)]) + [(k, i) for i in [0, 1, 2, 7, 8, 9]]
    assert count_even(10, pinned_edges, (1 << 7) | (1 << 8) | (1 << 9)) == count_even(6, cover(3, [(0, 1), (1, 2)]))
    print("single-gadget counts", local, "raw twin hosts", cases, "double covers", double_cases)


if __name__ == "__main__":
    test()
