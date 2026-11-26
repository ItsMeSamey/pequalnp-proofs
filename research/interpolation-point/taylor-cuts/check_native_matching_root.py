from fractions import Fraction
from itertools import product
from math import prod
from random import Random
rng = Random(26011)
for trial in range(500):
    m = rng.randrange(1,8)
    ports = list(range(m))*2
    rng.shuffle(ports)
    clauses = []
    while ports and rng.randrange(5):
        d = min(len(ports), rng.randrange(1,5))
        clauses.append(ports[:d])
        del ports[:d]
    actual = sum(prod(sum(b[j] for j in c) for c in clauses)
                 for b in product(range(2), repeat=m))
    edges = []
    for j in range(m):
        hits = [i for i,c in enumerate(clauses) for v in c if v==j]
        if len(hits)==2 and hits[0]!=hits[1]:
            edges.append(hits)
    total = 0
    for mask in product(range(2),repeat=len(edges)):
        hits = [i for k,e in enumerate(edges) if mask[k] for i in e]
        if len(set(hits))==len(hits):
            total += prod(len(c) for i,c in enumerate(clauses) if i not in hits)
    assert Fraction(2)**(m-len(clauses))*total==actual
print("500 exact incidence fixtures passed")
