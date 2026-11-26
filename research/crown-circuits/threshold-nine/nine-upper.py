"""A 21-gate monotone threshold-two circuit on nine row-major grid inputs."""
ops = []
def gate(op, a, b):
    ops.append((op, a, b))
    return 8 + len(ops)
def triple_any(a, b, c):
    return gate('OR', gate('OR', a, b), c)
def two_of_three(a, b, c):
    pair = gate('AND', a, b)
    third_pair = gate('AND', gate('OR', a, b), c)
    return gate('OR', pair, third_pair)

rows = [triple_any(3*i, 3*i+1, 3*i+2) for i in range(3)]
cols = [triple_any(j, j+3, j+6) for j in range(3)]
out = gate('OR', two_of_three(*rows), two_of_three(*cols))
assert len(ops) == 21
for pattern in range(512):
    wires = [bool(pattern & (1 << i)) for i in range(9)]
    for op, a, b in ops:
        wires.append((wires[a] or wires[b]) if op == 'OR' else (wires[a] and wires[b]))
    assert wires[out] == (pattern.bit_count() >= 2)
print('validated 21-gate upper bound on all 512 assignments')
