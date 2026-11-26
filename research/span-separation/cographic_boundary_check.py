"""Compare boundary operations and single-attachment summaries with exhaustive colorings."""
from itertools import product
from random import Random


def components(vertices, edges):
    pieces = [{x} for x in vertices]
    for x, y in edges:
        a = next(p for p in pieces if x in p)
        b = next(p for p in pieces if y in p)
        if a is not b:
            a.update(b)
            pieces.remove(b)
    return pieces


def state(color, boundary, blocks, closed, sums):
    return (tuple(color[x] for x in sorted(boundary)), tuple(sorted(tuple(sorted(g)) for g in blocks)),
            frozenset(closed), tuple(sums))


def table(vertices, edges, boundary, labels, b):
    out = set()
    for values in product(range(b), repeat=len(vertices)):
        color = dict(zip(sorted(vertices), values))
        pieces = components(vertices, [(x, y) for x, y in edges if color[x] == color[y]])
        closed = set()
        for p in pieces:
            if not p & boundary:
                i = color[next(iter(p))]
                if i in closed or any(color[v] == i for v in vertices - p):
                    break
                closed.add(i)
        else:
            sums = [0] * b
            for x in vertices - boundary:
                sums[color[x]] ^= labels[x]
            out.add(state(color, boundary, [p & boundary for p in pieces if p & boundary], closed, sums))
    return out


def forget(before, boundary, x, labels):
    after = set()
    for col, blocks, closed, sums in before:
        color = dict(zip(sorted(boundary), col))
        i = color[x]
        containing = next(g for g in blocks if x in g)
        remain = [set(g) - {x} for g in blocks if g != (x,)]
        if len(containing) == 1:
            if any(color[next(iter(g))] == i for g in remain):
                continue
            closed = closed | {i}
        sums = list(sums)
        sums[i] ^= labels[x]
        after.add(state(color, boundary - {x}, remain, closed, sums))
    return after


def introduce(before, boundary, x, b):
    after = set()
    for col, blocks, closed, sums in before:
        color = dict(zip(sorted(boundary), col))
        for i in set(range(b)) - closed:
            color[x] = i
            after.add(state(color, boundary | {x}, [*blocks, {x}], closed, sums))
    return after


def add_edge(before, boundary, u, v):
    out = set()
    for col, blocks, closed, sums in before:
        color = dict(zip(sorted(boundary), col))
        pieces = [set(g) for g in blocks]
        if color[u] == color[v]:
            a = next(g for g in pieces if u in g)
            c = next(g for g in pieces if v in g)
            if a is not c:
                a.update(c)
                pieces.remove(c)
        out.add(state(color, boundary, pieces, closed, sums))
    return out


def join(left, right, boundary):
    out = set()
    for col, blocks, closed, sums in left:
        for col2, blocks2, closed2, sums2 in right:
            if col != col2 or closed & (set(col2) | closed2) or closed2 & set(col):
                continue
            links = [(g[0], x) for g in (*blocks, *blocks2) for x in g[1:]]
            pieces = components(boundary, links)
            out.add(state(dict(zip(sorted(boundary), col)), boundary, pieces, closed | closed2,
                          [a ^ c for a, c in zip(sums, sums2)]))
    return out


def check_operations():
    rng = Random(559)
    joins = forgets = intros = edge_adds = 0
    for _ in range(140):
        n = rng.randint(2, 7)
        b = rng.randint(1, 3)
        overlap = set(range(rng.randint(0, min(n, 3))))
        remaining = sorted(set(range(n)) - overlap)
        split = rng.randrange(len(remaining) + 1)
        lvs = set(remaining[:split]) | overlap
        rvs = set(remaining[split:]) | overlap
        labels = [rng.randrange(4) for _ in range(n)]
        edges = [(v, w) for v in range(n) for w in range(v) if rng.random() < .4]
        le = [(a, c) for a, c in edges if a in lvs and c in lvs]
        re = [(a, c) for a, c in edges if a in rvs and c in rvs and (a, c) not in le]
        lt = table(lvs, le, overlap, labels, b)
        rt = table(rvs, re, overlap, labels, b)
        joined = join(lt, rt, overlap)
        combined = table(lvs | rvs, le + re, overlap, labels, b)
        assert joined == combined
        joins += 1
        for x in overlap:
            assert forget(joined, overlap, x, labels) == table(lvs | rvs, le + re, overlap - {x}, labels, b)
            forgets += 1
        assert introduce(lt, overlap, n, b) == table(lvs | {n}, le, overlap | {n}, labels + [0], b)
        intros += 1
        for u in overlap:
            for v in overlap:
                if u < v:
                    assert add_edge(joined, overlap, u, v) == table(lvs | rvs, le + re + [(u, v)],
                                                                    overlap, labels, b)
                    edge_adds += 1
    return joins, forgets, intros, edge_adds


if __name__ == "__main__":
    print("Verified joins, forgets, introductions, and edge additions:", check_operations())
