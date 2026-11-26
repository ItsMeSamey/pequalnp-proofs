"""Check rigid-group decompositions and rank-one PC on small graphs."""
from random import Random
from itertools import combinations
from collections import deque
from functools import lru_cache


@lru_cache(None)
def ring(n, degree):
    monomials = tuple(sum(1 << i for i in term)
                      for size in range(degree+1)
                      for term in combinations(range(n),size))
    pos = {mon:i for i,mon in enumerate(monomials)}
    low = sum(mon.bit_count()<degree for mon in monomials)
    multiply = tuple(tuple(1<<pos[mon | (1<<i)] for mon in monomials[:low])
                     for i in range(n))
    return pos, low, multiply


def pc(rows, labels, target, degree, width=3):
    n = len(rows)
    if degree < 2:
        raise ValueError("checker expects a degree of at least two")
    pos, low, multiply = ring(n,degree)
    queue = deque()
    for i,nb in enumerate(rows):
        p = 0
        for j in range(n):
            if nb>>j&1:
                p ^= 1 << pos[(1<<i)|(1<<j)]
        queue.append(p)
    for j in range(width):
        p = (target>>j)&1
        for i,c in enumerate(labels):
            if c>>j&1:
                p ^= 1 << pos[1<<i]
        queue.append(p)
    pivots = {}
    while queue:
        p = queue.popleft()
        while p and p.bit_length() in pivots:
            p ^= pivots[p.bit_length()]
        if p == 1:
            return True
        if not p:
            continue
        pivots[p.bit_length()] = p
        if p.bit_length() <= low:
            terms=[]
            q=p
            while q:
                bit=q&-q
                terms.append(bit.bit_length()-1)
                q^=bit
            for images in multiply:
                product=0
                for k in terms:
                    product ^= images[k]
                queue.append(product)
    return False



def groups(neutral, colors):
    by = {}
    for j, color in enumerate(colors):
        key = color, tuple((row >> j) & 1 for row in neutral)
        by[key] = by.get(key, 0) | (1 << j)
    return by


def rank(vectors):
    basis = {}
    for v in vectors:
        while v:
            i = v.bit_length() - 1
            if i not in basis:
                basis[i] = v
                break
            v ^= basis[i]
    return len(basis)


def full_solutions(rows, left_colors, right_colors):
    for x in range(1 << len(rows)):
        p = [sum((x >> i) & 1 for i, d in enumerate(left_colors) if d == c) % 2
             for c in (0, 1)]
        if sum(p) != 1:
            continue
        total = 0
        for i, row in enumerate(rows):
            if (x >> i) & 1:
                total ^= row
        for y in range(1 << len(right_colors)):
            q = [sum((y >> j) & 1 for j, d in enumerate(right_colors) if d == c) % 2
                 for c in (0, 1)]
            if p == q and not (y & total) and all(not (x >> i & 1) or
                not (row & y).bit_count() % 2 for i, row in enumerate(rows)):
                return True
    return False


def check(rows, lc, rc, pc):
    masks = [sum(1 << j for j, v in enumerate(rc) if v == c) for c in (0, 1)]
    neutral = [row for row, c in zip(rows, lc) if c is None]
    mixed = [row for row in neutral if all(row & mask for mask in masks)]
    if full_solutions(rows, lc, rc):
        return 0, 0
    for row, c in zip(rows, lc):
        if c is not None:
            assert row & masks[c] == masks[c]
    if rank(mixed) == rank(neutral):
        grouped = groups(mixed, rc)
        for mask in grouped.values():
            assert all((z & mask) in (0, mask) for z in neutral)
        for c in (0, 1):
            signatures = {}
            for row, color in zip(rows, lc):
                if color != c:
                    continue
                variations = [g for (d, _), g in grouped.items() if d != c and
                              (row & g) not in (0, g)]
                assert len(variations) <= 1
                if variations:
                    g, = variations
                    assert signatures.setdefault(g, row & ~g) == row & ~g
    if pc is not None and rank(neutral) <= 1:
        n = len(rows)
        graph = [a << n for a in rows] + [
            sum(1 << i for i, a in enumerate(rows) if (a >> j) & 1)
            for j in range(len(rc))]
        labels = [(0 if d is None else 1 | (4 * d)) for d in lc] + [2 | 4*d for d in rc]
        assert pc(graph, labels, 3, 3)
        return 1, 1
    return 1, 0


def main():
    rng = Random(607)
    count = nos = pcs = 0
    for _ in range(550):
        rc = [0, 0, 1, 1]
        lc = [0, 0, 1, 1, None, None]
        rows = [rng.randrange(16) | (3 if c == 0 else 12) if c is not None
                else rng.randrange(16) for c in lc]
        if rng.randrange(2):
            rows[-1] = rows[-2]
        a, b = check(rows, lc, rc, pc if pcs < 40 else None)
        count += 1
        nos += a
        pcs += b
    print(f'{count} seeded instances, {nos} negative cases, {pcs} degree-three saturations.')


if __name__ == '__main__':
    main()
