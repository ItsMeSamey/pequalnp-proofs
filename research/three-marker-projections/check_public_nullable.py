"""Trace the two native rotations including both private feedback rails."""
from itertools import product

def cycle_step(wire, cycle):
    if wire not in cycle:
        return wire
    return cycle[(cycle.index(wire) + 1) % len(cycle)]

def visible_return(bit, enable):
    observed = ('G', 'P', 'N')
    # z is the private third channel of the optional G/m transposition.
    stages = []
    if enable:
        stages.append(('G', 'm', 'z'))
    if bit:
        stages.append(('P', 'm', 'N'))
    stages.append(('P', 'm'))
    # z closes locally around its own stage; no later stage visits z.
    def lap(wire):
        for rotation in stages:
            wire = cycle_step(wire, rotation)
        return wire
    output = []
    for start in observed:
        wire = lap(start)
        while wire not in observed:
            wire = lap(wire)
        output.append(wire)
    return ''.join(output)

for bit, enable in product(range(2), repeat=2):
    out = visible_return(bit, enable)
    expected = ('GPN', ('PGN','NPG')[bit])[enable]
    assert out == expected, (bit, enable, out)
    print(bit, enable, out)
