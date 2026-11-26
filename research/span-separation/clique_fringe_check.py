"""Exhaustive colorings of small graphs with true clique attachments."""
from itertools import combinations, product
from random import Random


def components(vs, edges):
    left = set(vs)
    parts = []
    while left:
        todo = [left.pop()]
        seen = set(todo)
        while todo:
            v = todo.pop()
            for x, y in edges:
                if y == v:
                    x, y = y, x
                if x == v and y in left:
                    left.remove(y)
                    seen.add(y)
                    todo.append(y)
        parts.append(seen)
    return parts


def profile(col, labels, edges, boundary, b):
    sums = [0] * b
    used = set(col)
    for i, c in enumerate(col):
        if i not in boundary:
            sums[c] ^= labels[i]
    if any(len(components([v for v in range(len(col)) if col[v] == c], edges)) != 1 for c in used):
        return None
    bc = tuple(col[v] for v in sorted(boundary))
    return bc, tuple(sums), frozenset(used - set(bc))


def generate(rng):
    k = rng.randint(2, 4)
    core = set(range(k))
    edges = list(combinations(range(k), 2))
    n = k
    children = []
    for _ in range(rng.randint(1, 4)):
        adhesion = set(rng.sample(range(k), rng.randint(1, min(3, k))))
        new = set(range(n, n + rng.randint(1, 2)))
        n += len(new)
        # The default must handle several disconnected off-adhesion groups.
        local = []
        for v in new:
            local.append((v, rng.choice(sorted(adhesion))))
            local.extend((v, u) for u in adhesion if rng.random() < .35)
        if len(new) == 2 and rng.random() < .5:
            local.append(tuple(new))
        groups = components(new, local)
        defaults = {}
        for group in groups:
            root = next(y for x, y in local if x in group and y in adhesion)
            defaults.update({x: root for x in group})
        children.append((adhesion, new, defaults))
        edges.extend(local)
    return n, core, edges, children


def check(rng, b, r):
    while True:
        n, core, edges, children = generate(rng)
        if b ** n <= 23000:
            break
    labels = [rng.randrange(1 << r) for _ in range(n)]
    boundary = set(rng.sample(sorted(core), rng.randint(0, len(core))))
    cases = changed = max_repair = 0
    for col in product(range(b), repeat=n):
        before = profile(col, labels, edges, boundary, b)
        if before is None:
            continue
        candidate = list(col)
        residuals = []
        exception_colors = set()
        for adhesion, new, roots in children:
            inside = {col[v] for v in new} - {col[v] for v in adhesion}
            if inside:
                assert not inside & exception_colors
                exception_colors |= inside
                continue
            delta = 0
            for v, root in roots.items():
                target = col[root]
                delta ^= labels[v] << (r * col[v])
                delta ^= labels[v] << (r * target)
                candidate[v] = target
            residuals.append((delta, new))
        total = 0
        basis = {}
        for j, (delta, _) in enumerate(residuals):
            total ^= delta
            bitset = 1 << j
            while delta and delta.bit_length() in basis:
                k, c = basis[delta.bit_length()]
                delta ^= k
                bitset ^= c
            if delta:
                basis[delta.bit_length()] = delta, bitset
        selected = 0
        while total:
            d, c = basis[total.bit_length()]
            total ^= d
            selected ^= c
        assert selected.bit_count() <= r * (b - 1)
        max_repair = max(max_repair, selected.bit_count())
        for j, (_, new) in enumerate(residuals):
            if selected >> j & 1:
                for v in new:
                    candidate[v] = col[v]
        assert all(candidate[v] == col[v] for v in core)
        assert profile(candidate, labels, edges, boundary, b) == before
        changed += tuple(candidate) != col
        cases += 1
    return cases, changed, max_repair


if __name__ == "__main__":
    rng = Random(507)
    results = [check(rng, b, r) for b, r in product((2, 3), (1, 2)) for _ in range(12)]
    print(f"{len(results)} clique-fringe graphs, {sum(x for x, _, _ in results)} admissible colorings, "
          f"{sum(y for _, y, _ in results)} changed while preserving exact parent signature, "
          f"maximum {max(z for _, _, z in results)} retained deviations.")
