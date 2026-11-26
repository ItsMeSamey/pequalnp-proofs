"""Reconcile the two disjoint independent helper-kernel runs."""
from collections import Counter
from pathlib import Path
from hashlib import sha256

root = Path(__file__).resolve().parent
def read_rows(path):
    return [tuple(map(int, line.split())) for line in path.read_text().splitlines()]
rows = read_rows(root / "ledger.txt") + read_rows(root / "remaining-ledger.txt")
rows.sort()
assert [row[0] for row in rows] == list(range(25601))
assert all(len(row) == 4 and row[2] >= 1 and row[3] == 0 for row in rows)
assert Counter(row[1] for row in rows) == {0: 18089, 1: 6400, 2: 1027, 3: 85}
orig = read_rows(Path("/workspace/scratch/crown18264/threshold-six-minors/ten-six-census.txt"))
assert len(orig) == len(rows)
assert all((row[0], row[1], row[3]) == (a[0], a[2], a[4]) for row, a in zip(rows, orig))
print(f"{len(rows)} profiles, {sum(r[2] for r in rows)} helper libraries, zero feasible")
for q in range(4):
    bucket = [r for r in rows if r[1] == q]
    print(q, len(bucket), sum(r[2] for r in bucket))
print("Different helper-state counts from original", sum(r[2] != a[3] for r, a in zip(rows, orig)))
for name in ("helper.cpp", "controls.cpp", "ledger.txt", "remaining-ledger.txt"):
    print(sha256((root / name).read_bytes()).hexdigest(), name)
