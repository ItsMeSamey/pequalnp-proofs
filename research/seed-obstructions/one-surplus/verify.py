"""Check zero-line negative witnesses against the original theorem samples."""

import json
from pathlib import Path

from verify_packing import samples


root = Path(__file__).resolve().parent
rows, _, target = samples(root / "L-meta-18968.json")
if len(rows) != 676:
    raise ValueError("Expected the pinned theorem's 676 sample rows")

witnesses = json.loads((root / "zero-line-negative-witnesses.json").read_text())
point_sets = {(a, b) for a in range(13) for b in range(a + 1)}
if set(witnesses) != {f"{a},{b}" for a, b in point_sets}:
    raise ValueError("Witness list must cover every singleton and pair")

for a, b in point_sets:
    index = witnesses[f"{a},{b}"]
    mask = (1 << a) | (1 << b)
    if not 0 <= index < len(rows) or (target >> index) & 1 or rows[index] & mask != mask:
        raise ValueError(f"Row {index} fails to witness point set {a},{b}")

print(f"{len(point_sets)} zero-line point sets are dominated by sampled negatives.")
