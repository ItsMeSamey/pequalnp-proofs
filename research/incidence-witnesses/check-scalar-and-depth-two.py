"""Bounded differential check of the local proof cases on the Fano plane.

The tested predicate rejects every independent assignment with up to four
query raws; this local experiment does not use the order-two sparse promise.
"""
from collections import Counter
from itertools import product
from random import Random

rng = Random(573019)
points = range(7)
lines = range(7, 14)
flags = {(p, 7 + l) for p in points for l in points
         if (p - l) % 7 in (0, 1, 3)}
raws = list(range(14))
false = set(product(points, lines)) - flags
counts = Counter()


def passes(clauses, p, l):
    return all(p in clause or l in clause for clause in clauses)


def independent(raw_set):
    selected = set(raw_set)
    return not any((p, l) in flags for p in selected if p < 7
                   for l in selected if l >= 7)


def classify(left, right, p, l):
    clauses = left + right
    query_witnesses = [c for c in clauses if p not in c and l in c and
                       all((p, b) in flags for b in c if b >= 7)]
    point_witnesses = [c for c in clauses if l not in c and p in c and
                       all((x, l) in flags for x in c if x < 7)]
    assert query_witnesses and point_witnesses
    pc, qc = point_witnesses[0], query_witnesses[0]
    if sum(x < 7 for x in pc) > 1 or sum(b >= 7 for b in qc) > 1:
        return 'exact pool'
    if any(pc in side and qc in side for side in (left, right)):
        return 'same module'
    g, h = (left, right) if pc in left else (right, left)
    assert qc in h
    row_false = {b for x, b in false if x == p and passes(g, p, b)}
    column_false = {x for x, b in false if b == l and passes(h, x, l)}
    if len(row_false) <= 1:
        assert len(g) == 2
        sibling = g[1] if g[0] == pc else g[0]
        assert l in sibling and p not in sibling
        assert {b for b in sibling if b >= 7 and (p, b) not in flags} <= row_false
        return 'low row'
    if len(column_false) <= 1:
        assert len(h) == 2
        sibling = h[1] if h[0] == qc else h[0]
        assert p in sibling and l not in sibling
        assert {x for x in sibling if x < 7 and (x, l) not in flags} <= column_false
        return 'low column'
    high_rows = {x for x in points
                 if sum((x,b) in false and passes(g,x,b) for b in lines) >= 2}
    high_cols = {b for b in lines
                 if sum((x,b) in false and passes(h,x,b) for x in points) >= 2}
    assert set(product(high_rows,high_cols)) <= flags
    assert len(high_rows) == 1 or len(high_cols) == 1
    return 'high star'


for _ in range(15000):
    p, l = rng.choice(sorted(flags))
    def make_clause(anchor):
        return frozenset([anchor, *rng.sample(raws,rng.randrange(4))])
    left = [make_clause(rng.choice((p,l))) for _ in range(rng.randint(1,2))]
    right = [make_clause(rng.choice((p,l))) for _ in range(rng.randint(1,2))]
    clauses = left+right
    if any(independent(witness) for witness in product(*clauses)):
        continue
    counts['safe skeletons'] += 1
    for x, b in flags:
        if passes(clauses,x,b):
            counts[classify(left,right,x,b)] += 1
assert all(counts[name] for name in ('low row','low column','same module',
                                     'high star','exact pool'))
print(dict(sorted(counts.items())))
