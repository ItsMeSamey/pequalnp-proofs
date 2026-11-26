"""Ground hulls, adjacent model witnesses, and one-/multi-parity outcomes."""
from random import Random
from bijunctive_xor_hull import image, image_hull, prepare, solve


def cube_span(vectors):
    values = {0}
    for v in vectors:
        values |= {s ^ v for s in values}
    return values


def test(n, clauses, labels):
    models = {x for x in range(1 << n)
              if all(any(bool(x >> (abs(l)-1) & 1) == (l>0) for l in c) for c in clauses)}
    prepared = prepare(n, clauses)
    assert (prepared is None) == (not models)
    if prepared is None:
        return
    base, blocks = prepared
    assert base in models
    deltas = []
    for mask, pairs in blocks:
        for delta, a, b in pairs:
            assert ((base & ~mask) | a) in models and ((base & ~mask) | b) in models
            assert a ^ b == delta
            deltas.append(delta)
    assert cube_span(x ^ base for x in models) == cube_span(deltas)
    origin, basis = image_hull(prepared, labels)
    values = {image(x, labels) for x in models}
    assert cube_span(v ^ origin for v in values) == cube_span(basis)
    for t in range(8):
        status, x = solve(n, clauses, labels, t)
        assert status in ("SAT", "UNSAT", "UNKNOWN")
        if status == "SAT":
            assert x in models and image(x, labels) == t
        elif status == "UNSAT":
            assert t not in values
    for functional in (1,3,7):
        scalar = [(v & functional).bit_count() % 2 for v in labels]
        for bit in (0,1):
            status, x = solve(n, clauses, scalar, bit)
            assert (status == "SAT") == any(image(y, scalar) == bit for y in models)
            assert status != "UNKNOWN"
            if status == "SAT":
                assert x in models and image(x, scalar) == bit


rows = [(1,),(-1,),(2,),(-2,),(1,2),(1,-2),(-1,2),(-1,-2)]
for mask in range(1<<len(rows)):
    test(2, [r for j,r in enumerate(rows) if mask >> j & 1], [1,3])
rng = Random(14637)
for _ in range(180):
    n = rng.randrange(1,7)
    clauses = [tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,3)))
               for _ in range(rng.randrange(11))]
    test(n, clauses, [rng.randrange(8) for _ in range(n)])
assert solve(2, [(-1,-2)], [1,2], 3) == ("UNKNOWN",None)
for target in range(4):
    status, x = solve(3, [(-1,-2)], [1,2,1], target)
    assert status == "SAT" and image(x,[1,2,1]) == target and x & 3 != 3
assert solve(0, [], [], 0) == ("SAT",0)
assert solve(0, [()], [], 0) == ("UNSAT",None)
print("256 exhaustive two-variable systems and 180 additional systems passed, including scalar witnesses and multi-XOR peeling.")
