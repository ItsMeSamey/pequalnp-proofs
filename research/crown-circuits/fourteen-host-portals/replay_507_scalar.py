import itertools
import json
from collections import Counter
from pathlib import Path

circuit = json.loads(Path(__file__).with_name("507-composed-39.json").read_text())
n = circuit["inputs"]
assert n == 14 and len(set(map(tuple, circuit["edges"]))) == n
counts = Counter(g[0] for g in circuit["gates"])
assert counts == {"AND": 9, "OR": 30}
accepted = 0
for assignment in itertools.product([False, True], repeat=n):
    wires = list(assignment)
    for op, left, right in circuit["gates"]:
        assert 0 <= left < len(wires) and 0 <= right < len(wires)
        wires.append(all((wires[left], wires[right])) if op == "AND" else any((wires[left], wires[right])))
    actual = wires[circuit["output"]]
    assert actual == (sum(assignment) >= 2), assignment
    accepted += int(actual)
print(f"PASS 16384 assignments, {accepted} accepted, 30 OR and 9 AND")
