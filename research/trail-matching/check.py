"""Independent perfect-matching completion test for the parity-trail reduction."""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations, permutations, product


class Graph:
    def __init__(self):
        self.adjacency = []

    def vertices(self, count):
        start = len(self.adjacency)
        self.adjacency.extend([0] * count)
        return list(range(start, start + count))

    def edge(self, u, v):
        assert u != v
        self.adjacency[u] |= 1 << v
        self.adjacency[v] |= 1 << u

    def clique(self, vertices):
        for u, v in combinations(vertices, 2):
            self.edge(u, v)


def perfect_matching(adjacency, remaining):
    """Try every mate of a surviving minimum-degree vertex, with memoization."""
    @lru_cache(None)
    def visit(mask):
        if not mask:
            return True
        best = None
        todo = mask
        while todo:
            bit = todo & -todo
            todo ^= bit
            mates = adjacency[bit.bit_length() - 1] & mask
            if not mates:
                return False
            if best is None or mates.bit_count() < best.bit_count():
                pivot, best = bit, mates
                if best.bit_count() == 1:
                    break
        while best:
            mate = best & -best
            best ^= mate
            if visit(mask ^ pivot ^ mate):
                return True
        return False
    return visit(remaining)


def pair_trails(masks):
    incoming, outgoing = defaultdict(list), defaultdict(list)
    for i, m in enumerate(masks):
        outgoing[m].append(i)
        incoming[m ^ (1 << i)].append(i)
    choices = []
    for m in outgoing:
        a, b = incoming[m], outgoing[m]
        if len(a) <= len(b):
            choices.append([list(zip(a, subset)) for subset in permutations(b,len(a))])
        else:
            choices.append([list(zip(subset,b)) for subset in permutations(a,len(b))])
    for selection in product(*choices):
        nxt = dict(pair for pairs in selection for pair in pairs)
        roots = sorted(set(range(len(masks))) - set(nxt.values()))
        paths = []
        for i in roots:
            path = [i]
            while path[-1] in nxt:
                path.append(nxt[path[-1]])
            paths.append(path)
        assert sorted(i for path in paths for i in path) == list(range(len(masks)))
        yield paths


def compile_graph(masks, offset, paths):
    graph = Graph()
    n = len(masks)
    ports = []
    for i in range(n):
        before, pivot, after, dummy = graph.vertices(4)
        graph.edge(dummy, pivot)
        graph.edge(before, after)
        graph.edge(dummy, after if (offset >> i) & 1 else before)
        ports.append((before, pivot, after))

    # Every transition has a pivot port. Its second endpoint is either a
    # start-mask port or a reservoir port if it occurs in no start mask.
    wire_end = {}
    free = []
    for path in paths:
        first, last = path[0], path[-1]
        start = masks[first]
        sources = [i for i in range(n) if start >> i & 1]
        start_ports = graph.vertices(1 + len(sources))
        parity_dummy = graph.vertices(len(start_ports) % 2)
        graph.clique(start_ports + parity_dummy)
        graph.edge(start_ports[0], ports[first][0])
        for i, v in zip(sources, start_ports[1:]):
            if i in wire_end:
                return None
            wire_end[i] = v
        for left, right in zip(path, path[1:]):
            graph.edge(ports[left][2], ports[right][0])
        free.append(ports[last][2])

    unwired = [i for i in range(n) if i not in wire_end]
    reservoir = graph.vertices(len(free) + len(unwired))
    for end, v in zip(free, reservoir):
        graph.edge(end, v)
    for i, v in zip(unwired, reservoir[len(free):]):
        wire_end[i] = v
    reservoir += graph.vertices(len(graph.adjacency) % 2)
    graph.clique(reservoir)
    marked = [(ports[i][1], wire_end[i]) for i in range(n)]
    for u,v in marked:
        graph.edge(u,v)
    return graph.adjacency, marked


def completes(adjacency, marked, assignment):
    adj = adjacency.copy()
    remaining = (1 << len(adj)) - 1
    for i, (u, v) in enumerate(marked):
        if assignment >> i & 1:
            assert remaining & (1 << u) and remaining & (1 << v)
            remaining ^= (1 << u) | (1 << v)
        else:
            adj[u] &= ~(1 << v)
            adj[v] &= ~(1 << u)
    return perfect_matching(adj, remaining)


def audit(n):
    solved = assignments = ineligible = 0
    for masks in product(range(1 << n), repeat=n):
        for paths in pair_trails(masks):
            for offset in range(1 << n):
                result = compile_graph(masks, offset, paths)
                if result is None:
                    ineligible += 1
                    continue
                solved += 1
                for assignment in range(1 << n):
                    expected = all(not (assignment >> i & 1)
                                   or (m & assignment).bit_count() % 2 == (offset >> i & 1)
                                   for i,m in enumerate(masks))
                    assert completes(*result, assignment) == expected, (masks,offset,paths,assignment)
                    assignments += 1
    return solved, assignments, ineligible


if __name__ == '__main__':
    for n in (1,2,3):
        s, a, skip = audit(n)
        print(f'n={n}: {s} eligible systems/pairings, {a} exact assignment checks, {skip} ineligible systems/pairings.')
