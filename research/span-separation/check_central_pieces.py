"""Compare normalized and unrestricted connected partitions on explicit pieces."""
from functools import reduce
from itertools import combinations, product
from operator import xor
from random import Random


def connected(part, adj):
    if not part:
        return False
    stack = [next(iter(part))]
    seen = set(stack)
    while stack:
        for v in adj[stack.pop()] & part - seen:
            seen.add(v)
            stack.append(v)
    return seen == part


def check(rng, many=False):
    s, r = 2, rng.randrange(1, 3)
    ncore = 2 if many else rng.randrange(3, 6)
    edges = [] if many else list(combinations(range(ncore), 2))
    regions = []
    n = ncore
    for _ in range(6 if many else rng.randrange(1, 5)):
        count = 2 if many else rng.randrange(1, min(3, ncore) + 1)
        ports = [0, 1] if many else rng.sample(range(ncore), count)
        # A private star can attach to one, two or three ports. The fixed
        # baseline assigns its centre to the first port.
        edges.extend((v, n) for v in ports)
        regions.append((ports, n))
        n += 1
    adj = [set() for _ in range(n)]
    for x, y in edges:
        adj[x].add(y)
        adj[y].add(x)
    labels = [1] * n if many else [rng.randrange(1 << r) for _ in range(n)]
    if many:
        r = 1
    full, restricted = set(), set()
    compressed = False
    for assignments in product(range(s), repeat=n):
        parts = [{v for v in range(n) if assignments[v] == i} for i in range(s)]
        if not all(connected(part, adj) for part in parts):
            continue
        sums = tuple(reduce(xor, (labels[v] for v in part), 0) for part in parts)
        full.add(sums)
        peripheral = set(range(s)) - set(assignments[:ncore])
        dev = [(ports, x) for ports, x in regions if assignments[x] != assignments[ports[0]]]
        unchanged = [e for e in dev if assignments[e[1]] in peripheral]
        free = [e for e in dev if e not in unchanged]
        vectors = []
        for ports, x in free:
            vectors.append((labels[x] << (r * assignments[x])) ^
                           (labels[x] << (r * assignments[ports[0]])))
        desired = reduce(xor, vectors, 0)
        keep = next(t for j in range(min(r*s, len(free)) + 1)
                    for t in combinations(range(len(free)), j)
                    if reduce(xor, (vectors[i] for i in t), 0) == desired)
        normalized = list(assignments)
        for idx, (ports, x) in enumerate(free):
            if idx not in keep:
                normalized[x] = normalized[ports[0]]
        compressed |= len(keep) < len(free)
        normparts = [{v for v in range(n) if normalized[v] == i} for i in range(s)]
        assert all(connected(part, adj) for part in normparts)
        assert sums == tuple(reduce(xor, (labels[v] for v in p), 0) for p in normparts)
        restricted.add(sums)
    assert full == restricted
    return compressed


if __name__ == "__main__":
    rng = Random(2712)
    for _ in range(100):
        check(rng)
    assert check(rng, many=True)
    print("100 mixed-port clique fixtures and parallel two-port routing fixture passed")
