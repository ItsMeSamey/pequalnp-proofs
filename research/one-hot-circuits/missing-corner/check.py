"""Check the lower-bound hypotheses and the matching monotone circuit."""
from itertools import product

m, n = 4, 6
target = 818815
rows = [{j for j in range(n) if target >> (n * i + j) & 1} for i in range(m)]
cols = [{i for i in range(m) if j in rows[i]} for j in range(n)]
assert all(any(not row <= other for other in rows) for row in rows)
assert all(any(not col <= other for other in cols) for col in cols)
a, b, c, d = 2, 3, 1, 2
assert a != b and c != d
assert c in rows[a] and d in rows[a] and c in rows[b] and d not in rows[b]
assert all(len(rows[i]) < n for i in (a, b))
assert all(len(cols[j]) < m for j in (c, d))

gates = [
    ("or", 7, 8), ("or", 10, 9), ("and", 1, 11),
    ("or", 2, 3), ("and", 13, 5), ("and", 2, 6),
    ("or", 0, 4), ("or", 16, 12), ("or", 17, 14), ("or", 18, 15),
]
assert len(gates) == m + n
actual = 0
for i, j in product(range(m), range(n)):
    wires = [x == i for x in range(m)] + [y == j for y in range(n)]
    for op, left, right in gates:
        assert op in {"and", "or"} and 0 <= left < len(wires) and 0 <= right < len(wires)
        x, y = wires[left], wires[right]
        wires.append(x and y if op == "and" else x or y)
    actual |= int(wires[-1]) << (n * i + j)
assert actual == target
print(f"Hypotheses verified; {len(gates)} gates; {m*n}/{m*n} cells; mask {actual}")
