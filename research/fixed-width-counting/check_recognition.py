"""Independent finite checks of the C1P/interval graph equivalence."""
from itertools import combinations, permutations
from random import Random


def marked_graph(rows, size):
    neighbors = [set() for _ in range(len(rows) + size)]
    for j in range(size):
        clique = [i for i, row in enumerate(rows) if j in row] + [len(rows) + j]
        for a, b in combinations(clique, 2):
            neighbors[a].add(b)
            neighbors[b].add(a)
    return neighbors


def interval_graph(graph):
    # Chordal iff simplicial elimination succeeds.
    vertices = set(range(len(graph)))
    remaining = vertices.copy()
    while remaining:
        for v in remaining:
            neighbors = graph[v] & remaining
            if all(b in graph[a] for a, b in combinations(neighbors, 2)):
                break
        else:
            return False
        remaining.remove(v)
    # A chordal graph is interval iff it has no asteroidal triple.
    components = []
    for v in vertices:
        unseen = vertices - graph[v] - {v}
        labels = {}
        while unseen:
            root = unseen.pop()
            stack = [root]
            while stack:
                u = stack.pop()
                labels[u] = root
                following = unseen & graph[u]
                unseen -= following
                stack.extend(following)
        components.append(labels)
    for triple in combinations(vertices, 3):
        for i, v in enumerate(triple):
            a, b = triple[(i + 1) % 3], triple[(i + 2) % 3]
            label = components[v].get(a)
            if label is None or label != components[v].get(b):
                break
        else:
            return False
    return True


def consecutive(rows, n):
    for order in permutations(range(n)):
        for row in rows:
            positions = [i for i, v in enumerate(order) if v in row]
            if positions and positions[-1] - positions[0] + 1 != len(positions):
                break
        else:
            return True
    return False


if __name__ == '__main__':
    rng = Random(731)
    count = 0
    for n in range(1, 7):
        for _ in range(200):
            rows = [{j for j in range(n) if rng.randrange(2)} for _ in range(rng.randrange(9))]
            assert interval_graph(marked_graph(rows, n)) == consecutive(rows, n)
            count += 1
    print(count, 'matrix comparisons passed')
