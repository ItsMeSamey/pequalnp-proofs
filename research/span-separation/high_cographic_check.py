#!/usr/bin/env python3
"""Independent checks of binary basis packing and connected switching on K_{t,t}."""
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from random import Random


def xor(values):
    out = 0
    for x in values:
        out ^= x
    return out


@lru_cache(None)
def span(generators):
    found = {0}
    for x in generators:
        found |= {v ^ x for v in found}
    return frozenset(found)


@lru_cache(None)
def spaces(r):
    return tuple(sorted({span(g) for k in range(r + 1)
                         for g in combinations(range(1, 2**r), k)}, key=lambda s: (len(s), sorted(s))))


def dim(s):
    return len(s).bit_length() - 1


def choose_space(labels, r, l):
    return min(spaces(r), key=lambda s: sum(x not in s for x in labels) + l * dim(s))


def pack(labels, s, l):
    """Find bases by direct backtracking over possible basis value sets and their multiplicities."""
    bases = [c for c in combinations(sorted(s - {0}), dim(s)) if span(c) == s]
    indices = {x: [i for i, y in enumerate(labels) if y == x] for x in s}
    def search(k):
        if k == 0:
            return []
        for basis in bases:
            if all(indices[x] for x in basis):
                chosen = [indices[x].pop() for x in basis]
                later = search(k - 1)
                if later is not None:
                    return [chosen, *later]
                for x, i in zip(basis, chosen):
                    indices[x].append(i)
        return None
    return search(l)


def audit_threshold():
    count = 0
    for n in range(5):
        for labels in combinations_with_replacement(range(8), n):
            for l in range(1, 4):
                s = choose_space(labels, 3, l)
                outside = sum(x not in s for x in labels)
                assert outside <= l * (3 - dim(s))
                for t in spaces(3):
                    if t <= s:
                        assert sum(x in s - t for x in labels) >= l * (dim(s) - dim(t))
                assert pack(labels, s, l) is not None
                count += 1
    return count


def part_sums(assignment, labels, b):
    sums = [0] * b
    for i, x in zip(assignment, labels):
        sums[i] ^= x
    return sums


def route_case(rng, kind):
    b, r = 3, 4
    l = b - 1
    t = b + 25 * l * r + 2
    n = 2 * t
    base = {'zero': [0], 'exceptional': [0, 3, 5, 6], 'full': list(range(16))}[kind]
    labels = [rng.choice(base) for _ in range(n)]
    # The three exceptional values sum to zero and span a plane disjoint from the dense plane.
    if kind == 'exceptional':
        labels[:3] = [8, 1, 9]
    labels[-1] ^= xor(labels)
    rng.shuffle(labels)
    s = choose_space(labels, r, l)
    exc = [i for i, x in enumerate(labels) if x not in s]
    assert (dim(s), len(exc)) == {'zero': (0, 0), 'exceptional': (2, 3), 'full': (4, 0)}[kind]
    bases = pack(labels, s, l)
    assert bases is not None
    toggles = set().union(*map(set, bases))
    anchors = rng.sample(sorted(set(range(n)) - set(exc) - toggles), b)
    desired = [rng.randrange(b) for _ in labels]
    required = part_sums(desired, labels, b)
    # Each tuple is (anchor owner, endpoint, endpoint is permanent).
    demand = [(desired[v], v, True) for v in exc]
    for owner, basis in enumerate(bases):
        demand.extend((part, v, False) for v in basis for part in (owner, b - 1))
    used = set(anchors) | set(exc) | toggles
    def socket(v):
        p = next(w for w in range(n) if w not in used and (v < t) != (w < t))
        used.add(p)
        return p
    # Reserve every socket before joining any pair, so even unused socket vertices are protected.
    ports = [(socket(anchors[i]), socket(v)) for i, v, _ in demand]
    groups = {v: i for i, v in enumerate(anchors)}
    def edge(a, b):
        return (a < t) != (b < t)
    for (i, v, keep), (a, c) in zip(demand, ports):
        middle = [] if edge(a, c) else [socket(a)]
        path = [anchors[i], a, *middle, c, v]
        assert len(set(path)) == len(path) and all(edge(x, y) for x, y in zip(path, path[1:]))
        for x in path[1:-1]:
            assert x not in groups
            groups[x] = i
        if keep:
            groups[v] = i
    for basis, i in zip(bases, range(l)):
        for v in basis:
            for part in (i, b - 1):
                assert any(j == part and edge(x, v) for x, j in groups.items())
    remaining = set(range(n)) - set(groups) - toggles
    while remaining:
        old = len(remaining)
        for v in list(remaining):
            found = next((j for x, j in groups.items() if edge(x, v)), None)
            if found is not None:
                groups[v] = found
                remaining.remove(v)
        assert len(remaining) < old
    owner = [groups.get(v, b - 1) for v in range(n)]
    for i, basis in enumerate(bases):
        delta = required[i] ^ part_sums(owner, labels, b)[i]
        moves = next(c for k in range(len(basis) + 1) for c in combinations(basis, k)
                     if xor(labels[v] for v in c) == delta)
        for v in moves:
            owner[v] = i
    assert part_sums(owner, labels, b) == required
    assert all(owner[v] == desired[v] for v in exc)
    for i in range(b):
        vs = [v for v in range(n) if owner[v] == i]
        assert len(vs) == 1 or (vs and any(v < t for v in vs) and any(v >= t for v in vs))
    return len(demand), len(exc)


if __name__ == "__main__":
    checks = audit_threshold()
    rng = Random(1057)
    examples = [route_case(rng, kind) for _, kind in product(range(10), ('zero', 'exceptional', 'full'))]
    print(f"Passed {checks} basis-packing conditions and {len(examples)} switching constructions "
          f"on K_205,205 with {sum(x for x, _ in examples)} routed demands and "
          f"{sum(y for _, y in examples)} prescribed exceptions.")
