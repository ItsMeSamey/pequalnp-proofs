"""Verify the 18-gate circuit and the restriction to L-meta-11026."""
import json
from itertools import product
from pathlib import Path

edges = [(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),
         (5,7),(7,9),(6,9),(6,8),(5,8)]
minor_edges = {(0,4),(1,4),(0,5),(2,5),(0,6),(3,6),
               (1,7),(2,7),(4,7),(1,8),(3,8),(5,8)}
image = [7,6,3,7,2,1,0,8,4,5]
assert {tuple(sorted((image[a], image[b]))) for a,b in edges} == minor_edges
gates = json.loads(Path(__file__).with_name("upper18.json").read_text())
assert len(gates) == 18
for inputs in product((False, True), repeat=10):
    values = list(inputs)
    for op, a, b in gates:
        assert op in ("or", "and") and 0 <= a < len(values) and 0 <= b < len(values)
        values.append(values[a] | values[b] if op == "or" else values[a] & values[b])
    assert values[-1] == any(inputs[a] and inputs[b] for a,b in edges)
print("All 1,024 inputs and the nine-input edge image verified.")
