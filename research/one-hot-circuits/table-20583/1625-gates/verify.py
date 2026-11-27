"""Check the physical circuit on all one-row/one-column inputs."""
import json
from pathlib import Path
here = Path(__file__).resolve().parent
rows = [int(line, 16) for line in (here / 'rows.hex').read_text().splitlines()]
gates = json.loads((here / 'circuit.json').read_text())
n = 128
assert len(rows) == n and all(0 <= row < 2 ** n for row in rows)
universe = (1 << (n * n)) - 1
row_block = (1 << n) - 1
first_column = sum(1 << (n*i) for i in range(n))
values = [row_block << (i*n) for i in range(n)]
values.extend(first_column << j for j in range(n))
for op, i, j in gates:
    assert type(op) is int and op in (0, 1) and type(i) is int and type(j) is int
    assert 0 <= i < len(values) and 0 <= j < len(values)
    left, right = values[i], values[j]
    values.append(left | right if op == 1 else left & right)
assert values[-1] == sum(row << (i*n) for i, row in enumerate(rows))
live = {len(values)-1}
for k in reversed(range(len(gates))):
    if 2*n+k in live:
        op, i, j = gates[k]
        live.add(i)
        live.add(j)
print(f'{len(gates)} physical gates; {sum(w >= 2*n for w in live)} live gates; {n*n} cells agree')
