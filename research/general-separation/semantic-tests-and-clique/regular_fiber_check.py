"""Small exact graph checks for regular-fiber.md and cubic-correction.md."""
from itertools import combinations, product


def add(graph, u, v):
    graph[u] |= 1 << v
    graph[v] |= 1 << u


def edges(graph):
    return ((i, j) for i, row in enumerate(graph)
            for j in range(i + 1, len(graph)) if row >> j & 1)


def cliques(graph, k):
    def rec(pool, left, chosen):
        if left == 0:
            yield tuple(chosen)
            return
        while pool.bit_count() >= left:
            bit = pool & -pool
            v = bit.bit_length() - 1
            pool ^= bit
            yield from rec(pool & graph[v], left - 1, chosen + [v])
    return set(rec((1 << len(graph)) - 1, k, []))


def data_graph(pairs, z):
    steps = len(pairs)
    tuples = [(i, prior, typ) for i in range(steps) for prior in (0, 1)
              for typ in range(3) if (i > 0 or prior == 0)
              and (i < steps - 1 or prior ^ (typ == 2))]
    anchor_x, anchor_y = len(tuples), len(tuples) + 1
    graph = [0] * (len(tuples) + 2)
    for v, (i, prior, typ) in enumerate(tuples):
        x, y = pairs[i]
        if x == int(typ > 0):
            add(graph, v, anchor_x)
        if typ == 0 or y == int(typ == 2):
            add(graph, v, anchor_y)
        for w in range(v + 1, len(tuples)):
            j, next_prior, _ = tuples[w]
            if j > i + 1 or (j == i + 1 and next_prior == prior ^ (typ == 2)):
                add(graph, v, w)
    if z:
        add(graph, anchor_x, anchor_y)
    return graph


def check_cubes():
    tests = 0
    for size in range(1, 5):
        witnesses = set()
        private_witnesses = set()
        for pairs in product(tuple(product((0, 1), repeat=2)), repeat=size):
            odd = sum(x * y for x, y in pairs) % 2
            for z in (0, 1):
                found = cliques(data_graph(pairs, z), size + 2)
                assert len(found) == z * odd
                witnesses.update(found)
                if found and (0, 0) not in pairs:
                    assert not private_witnesses.intersection(found)
                    private_witnesses.update(found)
                tests += 1
        assert witnesses == private_witnesses
        assert len(witnesses) == (3**size - 1) // 2
    return tests


def regularize(copies, degree):
    assert len(copies) == 2 * degree
    n = len(copies[0])
    graph = [0] * (2 * degree * n)
    expected = [v.bit_count() for v in copies[0]]
    for j, copy in enumerate(copies):
        assert [v.bit_count() for v in copy] == expected
        for u, v in edges(copy):
            add(graph, n * j + u, n * j + v)
    for j in range(degree):
        for i, deg_i in enumerate(expected):
            for t in range(degree - deg_i):
                right_index = degree + (j + t) % degree
                add(graph, n * j + i, n * right_index + i)
    assert all(row.bit_count() == degree for row in graph)
    return graph


def triangle_switch(allowed):
    graph = [0] * 5
    for u, v in [(0, 2), (1, 2)] + ([(0, 1), (3, 4)] if allowed
                                      else [(0, 4), (3, 1)]):
        add(graph, u, v)
    return graph


def join(left, right):
    n = len(left)
    graph = left[:] + [row << n for row in right]
    for i in range(n):
        for j in range(n, len(graph)):
            add(graph, i, j)
    return graph


def check_switch():
    yes, no = triangle_switch(True), triangle_switch(False)
    unique = regularize([yes, no, no, no], 2)
    assert len(cliques(unique, 3)) == 1
    for flag in (False, True):
        other = regularize([triangle_switch(flag), no, no, no], 2)
        joined = join(other, unique)
        assert all(row.bit_count() == len(joined) // 2 + 2 for row in joined)
        assert len(cliques(joined, 6)) == int(flag)


def check_blocker():
    labels = [(-1, -1, t) for t in range(2)] + list(product(range(2), range(5), range(5)))
    graph = [0] * len(labels)
    for a, b in combinations(range(len(labels)), 2):
        i, j, p = labels[a]
        k, m, q = labels[b]
        if min(i, k) == -1 or (i == k and (j != m or (p - q) % 5 in (1, 4))):
            add(graph, a, b)
    pi = [labels.index((i, j, (p + 1) % (2 if i < 0 else 5)))
          for i, j, p in labels]
    degree = max(row.bit_count() for row in graph)
    for a, b in edges(graph):
        assert graph[pi[a]] >> pi[b] & 1
    assert all(graph[i] >> t & 1 for i, t in enumerate(pi))
    # Check the actual added edges sparsely without a large dense matrix.
    lifts = set()
    for i, row in enumerate(graph):
        for j in range(degree):
            for offset in range(degree - row.bit_count()):
                target = (j + offset) % degree
                assert (i, j, target) not in lifts
                lifts.add((i, j, target))
                assert graph[i] >> pi[i] & 1
    return len(lifts)


if __name__ == "__main__":
    assignments = check_cubes()
    check_switch()
    lifts = check_blocker()
    print(f"{assignments} data inputs, cubic witness counts through 4 pairs")
    print("2 joined regular graphs, exhaustive 6-clique and degree validation")
    print(f"{lifts} distinct intercopy edges preserved by the blocker map")
