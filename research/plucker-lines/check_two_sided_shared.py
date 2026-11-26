"""Check the two-sided certificate search against every selected support."""
from itertools import combinations, product
from random import Random


def certificates(rows, left, right, complete):
    for mirror in (False, True):
        a, b = (right, left) if mirror else (left, right)
        def adjacent(i, j):
            return bool((rows[j] >> i if mirror else rows[i] >> j) & 1)
        u, d = [], []
        for j, s in enumerate(b):
            if s == 2:
                continue
            misses = [i for i, r in enumerate(a) if r != 2 and not adjacent(i, j)]
            if not misses:
                u.append(j)
            for i in misses:
                d.append((i, j))
                if a[i] == s:
                    yield mirror, [i], [j]
                for t, r in enumerate(a):
                    if r == 2 and not adjacent(t, j):
                        yield mirror, [i, t], [j]
        if d:
            i, j = d[0]
            for s, t in combinations(u, 2):
                if b[s] == b[t]:
                    continue
                ns = {v for v, c in enumerate(a) if c == 2 and adjacent(v, s)}
                nt = {v for v, c in enumerate(a) if c == 2 and adjacent(v, t)}
                if ns-nt and nt-ns and a[i] != b[j]:
                    v, w = next(iter(ns-nt)), next(iter(nt-ns))
                    if adjacent(v, j) and adjacent(w, j):
                        yield mirror, [i, v, w], [j, s, t]
    if complete:
        for i, r in enumerate(left):
            if r == 2:
                continue
            for j, s in enumerate(right):
                if s != r or not (rows[i] >> j & 1):
                    continue
                ts = [t for t, v in enumerate(left) if v == 2 and rows[t] >> j & 1]
                ws = [w for w, v in enumerate(right) if v == 2 and rows[i] >> w & 1]
                if ts and ws:
                    yield False, [i, ts[0]], [j, ws[0]]


def check(rows, left, right, complete):
    def classify(mask, labels):
        return (sum((mask >> i & 1) for i, s in enumerate(labels) if s != 2) % 2,
                sum((mask >> i & 1) for i, s in enumerate(labels) if s != 0) % 2)
    targets = set()
    ys = [(y, classify(y, right)) for y in range(1 << len(right))]
    for x in range(1 << len(left)):
        first, bit = classify(x, left)
        if not first:
            continue
        active = [rows[i] for i in range(len(left)) if x >> i & 1]
        odd = 0
        for row in active:
            odd ^= row
        for y, label in ys:
            if label == (1, bit) and not (y & odd) and all(not ((row & y).bit_count() % 2) for row in active):
                targets.add((x, y))
    found = next(certificates(rows, left, right, complete), None)
    if found is None:
        assert not targets, (rows, left, right, complete)
    else:
        mirror, a, b = found
        x, y = (b, a) if mirror else (a, b)
        assert (sum(1 << i for i in x), sum(1 << j for j in y)) in targets


if __name__ == "__main__":
    for colors in product(range(2), repeat=4):
        left = colors[:2] + (2,)
        right = colors[2:] + (2,)
        for graph in range(512):
            rows = [graph >> (3*i) & 7 for i in range(3)]
            check(rows, left, right, bool(graph & 256))
    rng = Random(5161)
    for _ in range(3000):
        left = [rng.randrange(3) for _ in range(rng.randrange(1, 7))]
        right = [rng.randrange(3) for _ in range(rng.randrange(1, 7))]
        complete = rng.randrange(2)
        rows = [sum((complete if r == s == 2 else rng.randrange(2)) << j for j, s in enumerate(right)) for r in left]
        check(rows, left, right, complete)
    print("Passed 8,192 exhaustive graphs and 3,000 seeded graphs.")
