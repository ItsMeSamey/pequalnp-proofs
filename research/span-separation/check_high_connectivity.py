"""Check algebraic part-sum criterion and construct noncomplete witnesses."""
from functools import lru_cache, reduce
from itertools import combinations, product
from operator import xor
from random import Random


def span(vectors):
    out = {0}
    for v in vectors:
        out |= {x ^ v for x in out}
    return frozenset(out)


@lru_cache(None)
def spaces(r):
    return {span(t) for j in range(r + 1) for t in combinations(range(1, 1 << r), j)}


def packing(labels, r, h):
    D = min(spaces(r), key=lambda s: (sum(x not in s for x in labels)
                                       + h * (len(s).bit_length() - 1), tuple(sorted(s))))
    outside = [i for i, x in enumerate(labels) if x not in D]
    buckets = {x: [i for i, y in enumerate(labels) if y == x] for x in D}
    d = len(D).bit_length() - 1
    candidates = [t for t in combinations(sorted(D - {0}), d) if span(t) == D]

    def choose(left):
        if not left:
            return []
        for t in candidates:
            if all(buckets[x] for x in t):
                used = [buckets[x].pop() for x in t]
                rest = choose(left - 1)
                if rest is not None:
                    return [used] + rest
                for x, i in zip(t, used):
                    buckets[x].append(i)
        return None

    bases = choose(h)
    assert bases is not None and len(outside) + h * d <= h * r
    return D, outside, bases


def actual(labels, s):
    states = {((0,) * s, 0)}
    for x in labels:
        expanded = set()
        for values, used in states:
            for i in range(s):
                nxt = list(values)
                nxt[i] ^= x
                expanded.add((tuple(nxt), used | 1 << i))
        states = expanded
    return {vals for vals, used in states if used == (1 << s) - 1}


def predicted(labels, D, outside, s):
    residues = set()
    for assignment in product(range(s), repeat=len(outside)):
        vals = [0] * s
        for part, vertex in zip(assignment, outside):
            vals[part] ^= labels[vertex]
        residues.add(tuple(vals))
    target_total = reduce(xor, labels, 0)
    return {tuple(a ^ b for a, b in zip(v, ds))
            for v in residues for ds in product(D, repeat=s)
            if reduce(xor, v, 0) ^ reduce(xor, ds, 0) == target_total}


def sample_bipartite(rng, r, h):
    side = 22 * (r + 1) ** 2
    n = 2 * side
    common_bits = rng.randrange(r + 1)
    labels = [rng.randrange(1 << common_bits) for _ in range(n)]
    for _ in range(rng.randrange(2 * r + 1)):
        labels[rng.randrange(n)] = rng.randrange(1 << r)
    labels[-1] ^= reduce(xor, labels, 0)
    D, exc, bases = packing(labels, r, h)
    exc_parts = {v: rng.randrange(h + 1) for v in exc}
    goals = [0] * (h + 1)
    for v, i in exc_parts.items():
        goals[i] ^= labels[v]
    for i in range(1, h + 1):
        goals[i] ^= rng.choice(sorted(D))
    goals[0] = reduce(xor, goals[1:], 0)
    toggles = {v: i for i, basis in enumerate(bases, 1) for v in basis}
    reserved = set(toggles) | set(exc)
    roots = [v for v in range(side) if v not in reserved][:h + 1]
    reserved.update(roots)
    group = {v: i for i, v in enumerate(roots)}
    group.update(exc_parts)
    spare = iter(v for v in range(side, n) if v not in reserved)
    # All roots lie on the left. Direct cross edges or distinct right-side ports
    # realize every demand without another branch as an internal vertex.
    for v, idx in [*exc_parts.items(), *toggles.items(), *((v, 0) for v in toggles)]:
        if v < side:
            group[next(spare)] = idx
    # Give each root a right-side neighbor, then attach other leftovers at root zero.
    for i in range(h + 1):
        group[next(spare)] = i
    for v in range(n):
        group.setdefault(v, 0)
    current = [0] * (h + 1)
    for v, i in group.items():
        current[i] ^= labels[v]
    for i, basis in enumerate(bases, 1):
        delta = current[i] ^ goals[i]
        correction = next(s for j in range(len(basis) + 1) for s in combinations(basis, j)
                          if reduce(xor, (labels[v] for v in s), 0) == delta)
        for v in correction:
            group[v] = i
    for i in range(h + 1):
        part = [v for v in range(n) if group[v] == i]
        assert any(v < side for v in part) and any(v >= side for v in part)
        assert reduce(xor, (labels[v] for v in part), 0) == goals[i]


if __name__ == "__main__":
    rng = Random(7209)
    for _ in range(200):
        r, s = rng.randint(1, 3), rng.randint(2, 3)
        n = rng.randint(s + (s - 1) * r, 13)
        labels = [rng.randrange(1 << r) for _ in range(n)]
        D, outside, bases = packing(labels, r, s - 1)
        assert actual(labels, s) == predicted(labels, D, outside, s)
    for _ in range(100):
        r = rng.randint(1, 4)
        sample_bipartite(rng, r, rng.randint(1, r))
    print("200 complete-graph part-sum catalogs and 100 complete-bipartite witness partitions passed")
