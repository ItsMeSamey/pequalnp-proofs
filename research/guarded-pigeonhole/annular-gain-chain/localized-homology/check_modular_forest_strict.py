"""Exhaust physical baselines and all opposite-parity references of the three-gate control."""
from itertools import product, combinations
from strict_forest_reference import circles, physical, swap

sigma = (0,3,4,6,7,8,1,2,5)
gates = [(0,1,2),(3,4,5),(6,7,8)]


def references(p, triples):
    for bits in product((0,1), repeat=len(triples)):
        baseline = physical(p, triples, bits)
        for chords in product(*(combinations(t,2) for t in triples)):
            ref = swap(baseline,chords)
            if len(circles(ref)) == len(circles(baseline)) + len(triples):
                yield bits,chords


assert not list(references(sigma,gates))
for bit in (0,1):
    q = physical(sigma,gates,[bit])
    outputs = []
    for x in (6,7):
        x=q[x]
        while x<3:
            x=q[x]
        outputs.append(x)
    assert tuple(outputs) == ((3,4),(4,3))[bit]
off=(0,1,2,6,7,8,3,4,5)
assert ((0,1),((4,5),(6,8))) in set(references(off,gates[1:]))
for h,expected in [((0,0,0),False),((1,0,0),True)]:
    assert any(3 in c and 4 in c for c in circles(physical(sigma,gates,h))) == expected
print("216 whole-network candidates rejected; both port states and outer reference verified.")
