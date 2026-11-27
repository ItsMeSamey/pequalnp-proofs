"""Exhaust the anonymous outside parity profiles in the four-terminal obstruction."""
from itertools import product


def profiles(count):
    return [m for m in range(16)
            if m.bit_count() <= count and (count - m.bit_count()) % 2 == 0]


checked = 0
for a, b, c in product(range(5), repeat=3):
    # Outside A there are a copies of (1,0), b of (0,1), c of (1,1).
    states = {(0, 0)}
    for qbit, zbit, count in ((1, 0, a), (0, 1, b), (1, 1, c)):
        states = {(u ^ (v if qbit else 0), w ^ (v if zbit else 0))
                  for u, w in states for v in profiles(count)}
    for Q, Z in product(range(16), repeat=2):
        wq, wz = Q.bit_count() + a+c, Z.bit_count() + b+c
        if wq % 2 or wz % 2 or wz < 4 or a+c < 2:
            continue
        if min(wq, (15^Q).bit_count() + a+c) < 4:
            continue
        in_u = (b == c == 0) or (a == b == 0)
        in_h = ((b == c == 0 and Z in (0, 15)) or
                (a == b == 0 and (Q^Z) in (0, 15)))
        if in_u and not in_h:
            continue
        checked += 1
        assert (Q, 15^Z) in states or (15^Q, 15^Z) in states, (a,b,c,Q,Z)
print(checked, 'allowable nongraphic patterns, all feasible')
