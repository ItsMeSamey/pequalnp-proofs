"""Check seven inconsistent odd-mass requirements at the global orbit minimum."""
from itertools import product

gates = [(0, 1, 2), (0, 1, 3)] * 2 + [(0, 1, 2)]
cert = [('00001', {0, 1, 2}), ('00001', {3}), ('00010', {0, 1, 3}),
        ('00111', {0, 1, 3}), ('10010', {0, 3}), ('10011', {0, 1, 3}),
        ('10110', {0, 2, 3})]


def layers(bits):
    p = list(range(4))
    yield p[:]
    for bit, (a, b, c) in zip(bits, gates):
        for v in (b, c):
            swap = {a: v, v: a} if bit == '1' else {}
            p = [swap.get(x, x) for x in p]
            yield p[:]


def orbits(p):
    remaining = set(range(4))
    parts = []
    while remaining:
        u = min(remaining)
        part = set()
        while u in remaining:
            part.add(u)
            remaining.remove(u)
            u = p[u]
        parts.append(part)
    return parts


perms = {tuple(list(layers(mask))[-1]) for mask in product('01', repeat=5)}
assert len(perms) == 12 and min(len(orbits(p)) for p in perms) == 2
support = set()
for mask, initial in cert:
    steps = list(layers(mask))
    parts = orbits(steps[-1])
    assert len(parts) == 2 and initial in parts
    support.symmetric_difference_update(
        (j, p[x]) for j, p in enumerate(steps) for x in initial)
assert not support and len(cert) % 2 == 1
print('12 even permutations; minimum 2; seven optimal cycles XOR to zero on 44 positions')
