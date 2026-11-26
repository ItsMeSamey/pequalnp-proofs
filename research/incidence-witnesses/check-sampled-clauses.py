"""Check canonical clause uniqueness and shared OR construction on the Fano plane."""
from itertools import combinations

N = 7
lines = [sum(1 << ((i + d) % N) for d in (0, 1, 3)) for i in range(N)]
side = (1 << N) - 1
full = (1 << (2 * N)) - 1
edges = [(1 << p) | (1 << (N + j)) for j in range(N) for p in range(N)
         if lines[j] >> p & 1]
negatives = []
for size in range(3):
    for subset in combinations(range(N), size):
        covered = 0
        for j in subset:
            covered |= lines[j]
        negatives.append((side ^ covered) | sum(1 << (N + j) for j in subset))

for neg in negatives:
    assert all(neg & edge != edge for edge in edges)
    for bit in range(2 * N):
        if not (neg >> bit & 1):
            augmented = neg | 1 << bit
            assert any(augmented & edge == edge for edge in edges)
    clause = full ^ neg
    assert sum((other & clause) == 0 for other in negatives) == 1

gates = []
def combine(op, wires):
    wires = list(wires)
    assert wires
    root = wires[0]
    for other in wires[1:]:
        gates.append((op, root, other))
        root = 2 * N + len(gates) - 1
    return root

block = len(negatives).bit_length() - 1
tables = []
for start in range(0, 2 * N, block):
    size = min(block, 2 * N - start)
    table = {}
    for mask in range(1, 1 << size):
        bit = mask & -mask
        wire = start + bit.bit_length() - 1
        table[mask] = (wire if mask == bit else
                       combine('OR', [wire, table[mask ^ bit]]))
    tables.append((start, (1 << size) - 1, table))
clauses = []
for neg in negatives:
    selected = []
    for start, window, table in tables:
        mask = ((full ^ neg) >> start) & window
        if mask:
            selected.append(table[mask])
    clauses.append(combine('OR', selected))
output = combine('AND', clauses)

def evaluate(mask):
    values = [bool(mask >> i & 1) for i in range(2 * N)]
    for op, a, b in gates:
        values.append((values[a] or values[b]) if op == 'OR' else
                      (values[a] and values[b]))
    return values[output]

assert all(evaluate(mask) for mask in edges)
assert all(not evaluate(mask) for mask in negatives)
for assignment in range(1 << (2 * N)):
    if (assignment >> N).bit_count() <= 2:
        assert evaluate(assignment) == any(assignment & e == e for e in edges)
print(f"{len(edges)} positives, {len(negatives)} distinct forced clauses, {len(gates)} constructed gates")
