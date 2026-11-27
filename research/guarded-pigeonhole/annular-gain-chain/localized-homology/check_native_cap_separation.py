"""Trace every setting and test the 24 return caps for the acyclic patch."""

from itertools import permutations, product


def output_wire(start, mask):
    rail = start
    for on, slots in zip(mask, [(1, 2, 3), (0, 1, 2), (0, 1, 3)]):
        if on and rail in slots:
            rail = slots[(slots.index(rail) + 1) % 3]
    return rail


def orbit(start, perm):
    seen = set()
    while start not in seen:
        seen.add(start)
        start = perm[start]
    return seen


table = {
    tuple(output_wire(rail, mask) for rail in range(4))
    for mask in product(range(2), repeat=3)
}
assert sorted("".join(map(str, t)) for t in table) == [
    "0123", "0231", "1032", "1203", "1320", "3102", "3210"
]
assert any(t[0] == 0 for t in table) and any(t[3] == 2 for t in table)
assert all(t[0] != 2 and (t[0], t[3]) != (0, 2) for t in table)
for cap in permutations(range(4)):
    closed = [tuple(cap[o] for o in t) for t in table]
    for start in range(4):
        reachable = set().union(*(orbit(start, p) for p in closed))
        assert reachable == set(range(4))
print("Eight settings give seven permutations. Every cap joins each of its six pairs.")
