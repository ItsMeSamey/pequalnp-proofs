"""Ground comparisons, unlabeled graph-FPHP fixtures, and exact rejection tests."""
from fractions import Fraction
from itertools import combinations, product
from random import Random
from affine_resource_cliques import discover_cliques, resource_certificate, verify


def fixture(pigeons, holes, degree, rng):
    # Circulant with deliberate equalities broken by signed variable renaming.
    assert 1 <= degree <= holes <= pigeons
    edges = [(p, (p+j) % holes) for p in range(pigeons) for j in range(degree)]
    ids = rng.sample(range(1, len(edges)+1), len(edges))
    events = dict(zip(edges, [x * rng.choice((-1, 1)) for x in ids]))
    demands = [[lit for (p, _), lit in events.items() if p == i] for i in range(pigeons)]
    capacities = [[lit for (_, h), lit in events.items() if h == i] for i in range(holes)]
    clauses = [list(row) for row in demands]
    for group in demands + capacities:
        clauses += [[-a, -b] for a, b in combinations(group, 2)]
    for c in clauses:
        rng.shuffle(c)
    rng.shuffle(clauses)
    n = len(edges)
    found = discover_cliques(n, clauses)
    geometric = {tuple(sorted(row)) for row in demands + capacities if len(row) >= 2}
    extras = {tuple(sorted(-v for v in row)) for row in demands if len(row) == 2}
    assert found == geometric | extras
    cert = resource_certificate(n, clauses)
    if pigeons == holes:
        assert cert is None
        # Each pigeon has its diagonal edge available: exhibit a satisfying assignment.
        chosen = {abs(v): (v > 0) == (p == h) for (p, h), v in events.items()}
        assert all(any(chosen[abs(v)] == (v > 0) for v in c) for c in clauses)
    else:
        assert cert is not None and verify(n, clauses, cert)
        assert verify(n, clauses, [(k, r, Fraction(7, 9)) for k, r, w in cert])
        assert not verify(n, clauses, cert[:-1])
        assert not verify(n, clauses, cert + [("clause", tuple(clauses[0]), -1)])
        # Deleting a used native incompatibility invalidates the certificate.
        a, b = capacities[0][:2]
        reduced = [c for c in clauses if set(c) != {-a, -b}]
        assert not verify(n, reduced, cert)


rng = Random(1230481)
fixture(14, 7, 7, rng)
for iteration in range(50):
    for args in [(7, 5, 3), (10, 7, 4), (5, 5, 3), (3, 2, 2), (2, 1, 1)]:
        fixture(*args, rng)
# Signed event complementation is essential here.
assert verify(1, [(1,), (-1,)], [("clause",(1,),1), ("clause",(-1,),1)])
# An adjacent pair's common neighborhood need not be a clique.
diamond = [(-a, -b) for a, b in [(1,2),(1,3),(2,3),(1,4),(2,4)]]
assert (1,2,3,4) not in discover_cliques(4, diamond)
assert not verify(4, diamond, [("clique",(1,2,3,4),1)])
# Every locally witnessed row is valid on actual satisfying assignments, including
# signed random native CNFs for which the integral search may return no certificate.
for _ in range(200):
    n=5
    cnf = [[i*rng.choice((-1,1)) for i in rng.sample(range(1,n+1), rng.randrange(1,5))]
           for _ in range(rng.randrange(1,16))]
    found = discover_cliques(n, cnf)
    witnesses = [bits for bits in product((0,1), repeat=n)
                 if all(any(bits[abs(v)-1] == (v>0) for v in c) for c in cnf)]
    for bits in witnesses:
        for c in found:
            assert sum(bits[abs(v)-1] == (v>0) for v in c) <= 1
    cert = resource_certificate(n, cnf)
    assert cert is None or (not witnesses and verify(n, cnf, cert))
print("Recovered every hole and pigeon clique in 251 signed fixtures; 200 direct truth-table controls passed.")
