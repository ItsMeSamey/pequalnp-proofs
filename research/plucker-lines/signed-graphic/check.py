"""Small-instance checks. The large-instance linkage and SPQR routines are external."""
from itertools import combinations, product
from random import Random


def ends(path):
    return list(zip(path, path[1:]))


def edge(u, v):
    return min(u, v), max(u, v)


def paths(graph, a, b, banned=frozenset()):
    if a in banned or b in banned:
        return
    def visit(prefix):
        if prefix[-1] == b:
            yield prefix
            return
        for v in graph[prefix[-1]]:
            if v not in banned and v not in prefix:
                yield from visit(prefix + (v,))
    yield from visit((a,))


def parity(mask):
    return mask.bit_count() % 2


def cycle_test(rng):
    """Compare fixed-potential variation and total scores with the core reduction."""
    n = rng.randrange(3, 7)
    edges = [(0, 1)] + [e for e in combinations(range(n), 2)
                        if e != (0, 1) and rng.random() < .48]
    m = len(edges)
    signs, labels = (rng.getrandbits(m) for _ in range(2))
    w = rng.getrandbits(n)
    boundaries = [0]
    for a, b in edges:
        endmask = (1 << a) | (1 << b)
        boundaries += [s ^ endmask for s in boundaries]
    even = [i for i, b in enumerate(boundaries) if not b and i]
    simple = []
    for e in sorted(even, key=int.bit_count):
        if not any(e & q == q for q in simple):
            simple.append(e)
    roots = [q for q in simple if q & 1 and not parity(q & signs)]
    seconds = [q for q in simple if not q & 1 and
               not parity(q & signs) and parity(q & labels)]

    # Connected-component count on the edge union determines its cycle rank.
    def two_cycles(x):
        groups = [{a, b} for j, (a, b) in enumerate(edges) if x >> j & 1]
        merged = []
        for group in groups:
            keep = []
            for other in merged:
                if other & group:
                    group |= other
                else:
                    keep.append(other)
            merged = keep + [group]
        return x.bit_count() - sum(map(len, merged)) + len(merged) == 2

    pattern = any(two_cycles(q | p) for q in roots for p in seconds)
    variation = False
    all_costs, simple_costs = set(), set()
    for pot in range(1 << n):
        cut = sum((((pot >> a) ^ (pot >> b)) & 1) << j
                  for j, (a, b) in enumerate(edges))
        forbidden = cut ^ signs
        fixed = {parity(c & labels) for c in even if c & 1 and not c & forbidden}
        variation |= len(fixed) == 2
        offset = parity(pot & w)
        all_costs.update(z ^ offset for z in fixed)
        simple_costs.update(offset ^ parity(q & labels) for q in roots if not q & forbidden)
    assert variation == pattern
    assert all_costs == ({0, 1} if pattern else simple_costs)


def rigid_test(rng, mode):
    """Compute each rigid table twice, including arbitrary two-terminal child options."""
    n = rng.randrange(4, 8)
    # A wheel is 3-connected. Chords keep it 3-connected. Its reference edge is 01.
    all_edges = {edge(0, v) for v in range(1, n)}
    all_edges.update(edge(v, 1 + v % (n - 1)) for v in range(1, n))
    all_edges |= {e for e in combinations(range(n), 2) if rng.random() < .22}
    all_edges.remove((0, 1))
    graph = [set() for _ in range(n)]
    for u, v in all_edges:
        graph[u].add(v)
        graph[v].add(u)
    # Plant a switched balanced residual for the mandatory-feature stress modes.
    feature = 2 if mode == 1 else rng.choice(sorted(all_edges)) if mode == 2 else None
    switch = [rng.randrange(2) for _ in graph]
    features = set()
    if feature is not None:
        features.add(feature)
    if mode == 3:
        features |= {e for e in all_edges if rng.random() < .2}
        features |= {v for v in range(2, n) if rng.random() < .3}
    data = {}
    for u, v in sorted(all_edges):
        baseline = switch[u] ^ switch[v]
        touches = feature in ((u, v), u, v)
        signs = {baseline}
        if (mode in (1, 2) and touches) or (mode in (0, 3) and rng.random() < .3):
            signs.add(1 ^ baseline)
        table = {}
        for d in sorted(signs):
            first_cost = rng.randrange(2)
            for p in range(2):
                # Complementing every potential flips cost by the total internal weight.
                cost = first_cost ^ (p if (u, v) in features else 0)
                table[p, p ^ d] = {cost}
            if rng.random() < .2:
                for p in range(2):
                    table[p, p ^ d] = {0, 1}
        data[u, v] = table
    def costs(u, v, p, q):
        return (data[u, v].get((p, q), set()) if u < v else
                data[v, u].get((q, p), set()))
    def sums(a, b):
        return {x ^ y for x in a for y in b}
    def direct(path, p, q):
        states = {(p, 0)}
        for u, v in ends(path):
            states = {(d, c ^ z ^ (d if v in features else 0))
                      for a, c in states for d in (0, 1) for z in costs(u, v, a, d)}
        base = {z for d, z in states if d == q}
        covered = set(path) | {edge(u, v) for u, v in ends(path)}
        return {0, 1} if base and features - covered else base
    def avail(u, v):
        return {a ^ b for a, b in data[edge(u, v)]}
    def signed(path):
        total = {0}
        for u, v in ends(path):
            total = sums(total, avail(u, v))
        return total

    all_paths = list(paths(graph, 0, 1))
    nontrivial = 0
    for x, y in product(range(2), repeat=2):
        brute = set.union(set(), *(direct(path, x, y) for path in all_paths))
        viable = [p for p in all_paths if x ^ y in signed(p)]
        if not viable:
            result = set()
        elif any(features - (set(p) | {edge(u, v) for u, v in ends(p)}) for p in viable):
            result = {0, 1}
        elif not features:
            # No internal weights: child's sign+cost choices are start-potential independent.
            result = set()
            for path in viable:
                score = {(0, 0)}
                for u, v in ends(path):
                    score = {(s ^ d, c ^ z) for s, c in score for d in avail(u, v)
                             for z in costs(u, v, 0, d)}
                result.update(c for s, c in score if s == x ^ y)
        else:
            nontrivial += 1
            f = sorted(features, key=str)[0]
            residual = [set(neighbors) for neighbors in graph]
            removed = [e for e in all_edges if (f in e if isinstance(f, int) else f == e)]
            for u, v in removed:
                residual[u].remove(v)
                residual[v].remove(u)
            g = {0: 0}
            todo = [0]
            while todo:
                u = todo.pop()
                for v in residual[u]:
                    ss = avail(u, v)
                    assert len(ss) == 1
                    value = g[u] ^ next(iter(ss))
                    if v not in g:
                        g[v] = value
                        todo.append(v)
                    assert g[v] == value
            assert 1 in g and g[1] != (x ^ y)
            def arc_cost(path, switched):
                possible = {0}
                for u, v in ends(path):
                    possible = sums(possible, costs(u, v, g[u] ^ switched, g[v] ^ switched))
                load = sum(g[v] ^ switched for v in path if v in features) % 2
                return {c ^ load for c in possible}
            if isinstance(f, int):
                modes = [(u, v) for u in graph[f] for v in graph[f] if u != v]
            else:
                modes = [f, f[::-1]]
            result = set()
            for u, v in modes:
                if u not in g or v not in g:
                    continue
                p, q = g[u] ^ x, g[v] ^ g[1] ^ y
                local = costs(u, v, p, q) if not isinstance(f, int) else {
                    l ^ r ^ d for d in (0, 1)
                    for l in costs(u, f, p, d) for r in costs(f, v, d, q)}
                for first in paths(residual, 0, u):
                    for second in paths(residual, 1, v, set(first)):
                        result |= sums(local, sums(arc_cost(first, x), arc_cost(second, g[1] ^ y)))
        assert result == brute, (mode, features, x, y, result, brute)
    return nontrivial


if __name__ == '__main__':
    rng = Random(532115)
    for _ in range(300):
        cycle_test(rng)
    active = sum(rigid_test(rng, i % 4) for i in range(240))
    print(f"300 fiber/pattern and 960 rigid table comparisons passed; {active} mandatory entries.")
