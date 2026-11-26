"""Replay the rooted pivot-depth family, using vertex names and integer bitsets."""

from collections import deque


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def build(k):
    # 0,1,2,3,4 = A,B,C,T,U. Extra path interiors follow in path order.
    graph = [0] * (2 * k + 7)

    def edge(i, j):
        graph[i] |= 1 << j
        graph[j] |= 1 << i

    for hub in (0, 1):
        for neighbor in (2, 3, 4):
            edge(hub, neighbor)
    long_path = [0, *range(5, 5 + 2 * k), 2]
    short_path = [1, len(graph) - 2, len(graph) - 1, 2]
    for path in (long_path, short_path):
        for i, j in zip(path, path[1:]):
            edge(i, j)
    sequence = list(zip(long_path[1:-1:2], long_path[2:-1:2])) + [(1, 2)]
    return tuple(graph), sequence


def pivot(graph, i, j):
    assert graph[i] >> j & 1
    pair = (1 << i) | (1 << j)
    ni = graph[i] & ~pair
    nj = graph[j] & ~pair
    result = list(graph)
    for v in vertices(ni):
        result[v] ^= nj | pair
    for v in vertices(nj):
        result[v] ^= ni | pair
    result[i] = nj | (1 << j)
    result[j] = ni | (1 << i)
    return tuple(result)


ROOTS = (1 << 0) | (1 << 3)
MARK = 1 << 5


def feasible(graph, support):
    return all((graph[i] & support).bit_count() % 2 == 0 for i in vertices(support))


def generator(graph, support):
    if not graph[0] & (1 << 3):
        return support.bit_count() <= 3 and all(
            not graph[i] & support for i in vertices(support)
        )
    isolated = 0
    for i in vertices(support):
        degree = (graph[i] & support).bit_count()
        if degree == 0:
            isolated |= 1 << i
        elif degree != 2:
            return False
    if isolated.bit_count() > 1:
        return False
    seen = pending = 1
    while pending:
        bit = pending & -pending
        pending ^= bit
        new = graph[bit.bit_length() - 1] & support & ~seen
        pending |= new
        seen |= new
    return seen | isolated == support


def minimum_depth(graph):
    full = (1 << len(graph)) - 1
    seen = {0}
    queue = deque([(graph, 0, 0)])
    while queue:
        current, swapped, depth = queue.popleft()
        if generator(current, full ^ swapped):
            return depth
        for i in vertices(full & ~ROOTS):
            for j in vertices(current[i] & ~ROOTS & ((1 << i) - 1)):
                key = swapped ^ (1 << i) ^ (1 << j)
                if key not in seen:
                    seen.add(key)
                    queue.append((pivot(current, i, j), key, depth + 1))
    raise AssertionError("no generator chart")


def main():
    for k in range(1, 25):
        graph, sequence = build(k)
        full = (1 << len(graph)) - 1
        if k <= 5:
            fixed = ROOTS | MARK
            remaining = full ^ fixed
            subset = remaining
            while True:
                support = fixed | subset
                assert feasible(graph, support) == (support == full)
                if subset == 0:
                    break
                subset = (subset - 1) & remaining
        if k <= 4:
            assert minimum_depth(graph) == k + 1
        support = full
        for i, j in sequence:
            assert not ROOTS & ((1 << i) | (1 << j))
            assert support >> i & support >> j & 1
            graph = pivot(graph, i, j)
            support ^= (1 << i) | (1 << j)
            assert feasible(graph, support)
        assert generator(graph, support)
        assert support.bit_count() == 5 and graph[0] & (1 << 3)
    print("Unique marked witness k=1..5; exact BFS depth k=1..4; construction k=1..24.")


if __name__ == "__main__":
    main()
