"""Independently check the certificate extractor, sharp example and degree-three PC."""
from itertools import combinations, product
from random import Random


def certificate(rows, labels, colors):
    shared = [i for i, r in enumerate(labels) if r == 2]
    colored = [i for i, r in enumerate(labels) if r != 2]
    universal = []
    deficient = []
    for j, s in enumerate(colors):
        missing = [i for i in colored if not (rows[i] >> j & 1)]
        for i in missing:
            if labels[i] == s:
                return 1 << i, 1 << j
            for t in shared:
                if not (rows[t] >> j & 1):
                    return (1 << i) | (1 << t), 1 << j
        if missing:
            deficient.append((missing[0], j))
        else:
            universal.append(j)
    if deficient:
        i, j = deficient[0]
        for a, b in combinations(universal, 2):
            if colors[a] == colors[b]:
                continue
            left = [t for t in shared if rows[t] >> a & 1 and not (rows[t] >> b & 1)]
            right = [t for t in shared if rows[t] >> b & 1 and not (rows[t] >> a & 1)]
            if left and right:
                return sum(1 << t for t in [i, left[0], right[0]]), sum(1 << q for q in [j, a, b])
    return None


def models(rows, labels, colors):
    for x in range(1 << len(rows)):
        active = [i for i in range(len(rows)) if x >> i & 1]
        if sum(labels[i] != 2 for i in active) % 2 != 1:
            continue
        shared = sum(labels[i] != 0 for i in active) % 2
        wrong = 0
        for i in active:
            wrong ^= rows[i]
        for y in range(1 << len(colors)):
            if y.bit_count() % 2 == 0 or y & wrong:
                continue
            if any((rows[i] & y).bit_count() % 2 for i in active):
                continue
            if sum(s for j, s in enumerate(colors) if y >> j & 1) % 2 == shared:
                yield x, y


def pc_check(rows, labels, colors):
    # Work modulo Boolean squares, with all monomials of degree <= 3.
    n = len(rows) + len(colors)
    mons = sorted((sum(1 << i for i in subset) for d in range(4)
                   for subset in combinations(range(n), d)), key=lambda m: (m.bit_count(), m))
    coord = {m: 1 << i for i, m in enumerate(mons)}
    pivots = {}

    def insert(row):
        while row:
            lead = row.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = row
                break
            row ^= pivots[lead]

    def eq(ms):
        v = 0
        for m in ms:
            v ^= coord[m]
        insert(v)

    h = len(rows)
    eq([0] + [1 << i for i, r in enumerate(labels) if r != 2])
    eq([0] + [1 << (h+j) for j in range(len(colors))])
    eq([1 << i for i, r in enumerate(labels) if r != 0] +
       [1 << (h+j) for j, r in enumerate(colors) if r])
    for i, row in enumerate(rows):
        eq([(1 << i) | (1 << (h+j)) for j in range(len(colors)) if row >> j & 1])
    for j in range(len(colors)):
        eq([(1 << i) | (1 << (h+j)) for i, row in enumerate(rows) if row >> j & 1])
    # Adaptively multiply every new low-degree pivot. Degree order ensures these
    # span the entire currently derivable degree-at-most-two subspace.
    done = set()
    while 0 not in pivots:
        todo = [k for k in pivots if mons[k].bit_count() < 3 and k not in done]
        assert todo, "degree-three closure did not contain one"
        for k in todo:
            done.add(k)
            support = [m for l, m in enumerate(mons) if pivots[k] >> l & 1]
            for j in range(n):
                eq([m | (1 << j) for m in support])


def check(rows, labels, colors, audit=False):
    found = certificate(rows, labels, colors)
    valid = set(models(rows, labels, colors))
    assert (found in valid) if found is not None else not valid
    if audit and found is None:
        pc_check(rows, labels, colors)
        return 1
    return 0


if __name__ == "__main__":
    audits = 0
    # One shared label and two colored rows or two shared labels and one colored row.
    for ncolored in (1, 2):
        for lab in product(range(2), repeat=ncolored+2):
            labels = lab[:ncolored] + (2,) * (3-ncolored)
            colors = lab[ncolored:]
            for rows in product(range(4), repeat=3):
                audits += check(rows, labels, colors, audit=True)
    rng = Random(716)
    for i in range(2500):
        h, q = rng.randrange(1, 7), rng.randrange(1, 7)
        labels = [rng.randrange(3) for _ in range(h)]
        colors = [rng.randrange(2) for _ in range(q)]
        rows = [rng.getrandbits(q) for _ in labels]
        audits += check(rows, labels, colors, audit=(i < 500))
    # Right order a,b,j. Left order i,t,s.
    assert set(models([3, 5, 6], [0, 2, 2], [0, 1, 1])) == {(7, 7)}
    print(f"Checked 1,536 exhaustive and 2,500 seeded instances, {audits} degree-three refutations, and a sharp six-cycle.")
