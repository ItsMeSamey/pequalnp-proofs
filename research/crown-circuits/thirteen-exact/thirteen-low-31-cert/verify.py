import json
from pathlib import Path

circuit = json.loads(Path(__file__).with_name("size32.json").read_text())
inputs = circuit["inputs"]
gates = circuit["gates"]
size = 1 << inputs
assert inputs == 13 and len(gates) == 32 and circuit["output"] == 44
wires = [sum(1 << mask for mask in range(size) if mask >> i & 1) for i in range(inputs)]
for op, a, b in gates:
    assert 0 <= a < len(wires) and 0 <= b < len(wires)
    assert op in ("AND", "OR")
    wires.append(wires[a] & wires[b] if op == "AND" else wires[a] | wires[b])
expected = sum(1 << mask for mask in range(size) if mask.bit_count() >= 2)
assert wires[circuit["output"]] == expected
print(f"{len(gates)} gates, {sum(op == 'AND' for op, _, _ in gates)} AND, {size} inputs verified")
