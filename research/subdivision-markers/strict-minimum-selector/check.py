"""Exact small checks. Run with python check.py."""
from itertools import combinations, product
from random import Random


def rank(columns):
    pivots = {}
    for x in columns:
        while x:
            bit = x.bit_length()
            if bit in pivots:
                x ^= pivots[bit]
            else:
                pivots[bit] = x
                break
    return len(pivots)


def image(columns):
    space = {0}
    for x in columns:
        space |= {s ^ x for s in space}
    return space


def physical_minimum(d, gains, k, t):
    m, r = len(d), max((x.bit_length() for x in d), default=0)
    offset = m + 2*r
    columns = []
    for e, (col, (a, b)) in enumerate(zip(d, gains)):
        for v in (1, 2, 3):
            lo, hi = v & 1, v >> 1
            columns.append((1 << e) | ((lo * col) << m) |
                           ((hi * col) << (m+r)) | ((lo*a ^ hi*b) << offset))
    root = (1 << m)-1 | (t << offset)
    for size in range(len(columns)+1):
        for subset in combinations(columns, size):
            space = image(subset)
            if root in space and all((s << offset) not in space for s in range(1, 1 << k)):
                return size


def minima(d, gains, k):
    m = len(d)
    raw, exact = [None]*(1 << k), [None]*(1 << k)
    for f in product(range(4), repeat=m):
        a = b = t = 0
        for x, col, (s, u) in zip(f, d, gains):
            if x & 1:
                a ^= col
                t ^= s
            if x & 2:
                b ^= col
                t ^= u
        if a or b:
            continue
        z = [col for x, col in zip(f, d) if not x]
        if raw[t] is None or len(z) < raw[t]:
            raw[t] = len(z)
        if rank(z) == len(z) and (exact[t] is None or len(z) < exact[t]):
            exact[t] = len(z)
    return raw, exact


def edge_words(edges):
    vertex_count = 1 + max(max(edge) for edge in edges)
    words = []
    for word in range(1 << len(edges)):
        boundary = 0
        for i, (a, b) in enumerate(edges):
            if (word >> i) & 1:
                boundary ^= 1 << a
                boundary ^= 1 << b
        if not boundary:
            words.append(word)
    assert len(words) == 1 << (len(edges)-vertex_count+1)
    return words


def graph_minimum(edges):
    words = edge_words(edges)
    counts = [len(edges)-(x | y).bit_count() for x in words for y in words]
    return min(counts), counts.count(0)


def main():
    rng = Random(14347)
    checked = 0
    for k in range(4):
        for m in range(4):
            d = [rng.randrange(4) for _ in range(m)]
            tags = [(rng.randrange(1 << k), rng.randrange(1 << k)) for _ in d]
            raw, exact = minima(d, tags, k)
            if k <= 1:
                assert raw == exact
            for t, z in enumerate(exact):
                assert physical_minimum(d, tags, k, t) == (None if z is None else m+2*z)
                checked += 1
    assert minima([0], [(1, 2)], 2) == ([1, 0, 0, 0], [None, 0, 0, 0])
    k4 = list(combinations(range(4), 2))
    petersen = [(i, (i + 1) % 5) for i in range(5)]
    petersen += [(i + 5, (i + 2) % 5 + 5) for i in range(5)]
    petersen += [(i, i+5) for i in range(5)]
    assert graph_minimum(k4) == (0, 6)
    snark = graph_minimum(petersen)
    assert snark[1] == 0
    internal = [e for e in k4 if e != (0, 1)]
    for boundary in (1, 2, 3):
        choices = []
        for f in product((1, 2, 3), repeat=5):
            residual = [boundary, boundary, 0, 0]
            for edge, c in zip(internal, f):
                for a in edge:
                    residual[a] ^= c
            if not any(residual):
                choices.append(f)
        assert len(choices) == 2
        j = internal.index((0, 2))
        assert choices[0][j] ^ choices[1][j] == boundary
    print(checked, "physical target minima; K4 (0, 6); Petersen", snark,
          "; all three nonzero cut-open K4 boundary checks passed")


if __name__ == "__main__":
    main()
