"""Bounded oracle checks of the native flexible-chain quotient and original lift."""
from itertools import combinations
from random import Random


def parity_support(graph, selected):
    return all((len(graph[v] & selected) % 2 == 0) for v in selected)


def subsets(values):
    values = sorted(values)
    for size in range(len(values) + 1):
        for chosen in combinations(values, size):
            yield set(chosen)


def quotient(graph, pins):
    branch = pins | {v for v, neighbors in enumerate(graph) if len(neighbors) != 2}
    direct = []
    paths = []
    seen = set()
    for u in sorted(branch):
        for v in graph[u]:
            segment = frozenset((u, v))
            if segment in seen:
                continue
            seen.add(segment)
            previous, endpoint = u, v
            interior = []
            while endpoint not in branch:
                interior.append(endpoint)
                next_vertex, = graph[endpoint] - {previous}
                seen.add(frozenset((endpoint, next_vertex)))
                previous, endpoint = endpoint, next_vertex
            if interior:
                if u != endpoint:
                    paths.append((u, endpoint, interior))
            else:
                direct.append((u, endpoint))
    return branch, direct, paths


def forest_lift(occupied, direct, paths):
    demands = {v: 0 for v in occupied}
    network = {v: [] for v in occupied}
    for u, v in direct:
        if u in occupied and v in occupied:
            demands[u] ^= 1
            demands[v] ^= 1
    for u, v, interior in paths:
        if u in occupied and v in occupied:
            network[u].append((v, interior))
            network[v].append((u, interior))
    components = {}
    lifted = set(occupied)
    feasible = True
    for root in sorted(occupied):
        if root in components:
            continue
        components[root] = root
        order = [root]
        back = {}
        for v in order:
            for w, interior in network[v]:
                if w not in components:
                    components[w] = root
                    back[w] = (v, interior)
                    order.append(w)
        for w in reversed(order[1:]):
            if demands[w]:
                v, interior = back[w]
                demands[v] ^= 1
                lifted.update(interior)
        feasible &= demands[root] == 0
    return (lifted if feasible else None), components


def check(graph, pins):
    branch, direct, paths = quotient(graph, pins)
    possible = set()
    for extra in subsets(set(range(len(graph))) - pins):
        word = pins | extra
        if parity_support(graph, word):
            possible.add(frozenset(word & branch))
    for extra in subsets(branch - pins):
        occupied = pins | extra
        lifted, components = forest_lift(occupied, direct, paths)
        assert (lifted is not None) == (occupied in possible)
        if lifted is not None:
            assert lifted & branch == occupied and parity_support(graph, lifted)
        for fixed_selected in subsets(occupied - pins):
            fixed = pins | fixed_selected | (branch - occupied)
            if all(u not in occupied or v not in occupied or
                   components[u] == components[v] or {u, v} <= fixed
                   for u, v in direct):
                assert (lifted is not None) == any(
                    candidate & fixed == occupied & fixed for candidate in possible)
    return 1


def graph_from_edges(n, edges):
    graph = [set() for _ in range(n)]
    for u, v in edges:
        graph[u].add(v)
        graph[v].add(u)
    return graph


if __name__ == "__main__":
    cases = 0
    all_edges = list(combinations(range(5), 2))
    for mask in range(1 << len(all_edges)):
        graph = graph_from_edges(5, [e for i, e in enumerate(all_edges) if mask >> i & 1])
        for pins in combinations(range(5), 3):
            cases += check(graph, set(pins))
    rng = Random(21307)
    for _ in range(100):
        n = rng.randrange(6, 10)
        graph = graph_from_edges(n, [e for e in combinations(range(n), 2)
                                     if rng.randrange(3) == 0])
        cases += check(graph, set(rng.sample(range(n), 3)))
    print(f"{cases} original three-pin instances, every branch occupancy and certified face")
