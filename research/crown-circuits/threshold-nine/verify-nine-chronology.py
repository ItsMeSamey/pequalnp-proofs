"""Check each exceptional ledger row for the fourth-switch obstruction."""
from pathlib import Path
import sys

profiles, ledger = (Path(name) for name in sys.argv[1:])
activations = [tuple(map(int, row.split())) for row in profiles.read_text().splitlines()]
records = [row.split() for row in ledger.read_text().splitlines()]
assert len(records) == len(activations) == 25680
assert [int(row[0]) for row in records] == list(range(len(activations)))
expected = [5936, 9314, 20460, 20907, 25448, 25638]
positive = [int(row[0]) for row in records if int(row[4])]
assert positive == expected, positive
for index in positive:
    assert int(records[index][2]) == 0
    masks = activations[index]
    full = (1 << 64) - 1
    halves = [sum(1 << x for x in range(64) if (x >> j) & 1) for j in range(6)]
    branches = {a & h for a, h in zip(masks, halves)} | {a & (full ^ h) for a, h in zip(masks, halves)}
    assert sorted(a.bit_count() for a in set(masks) - branches - {full}) == [56, 60, 60]
    sizes = [a.bit_count() for a in masks]
    assert sizes[0] == 64 and all(s in (16, 32, 64) for s in sizes[:3])
    assert sizes[3:] == [56, 60, 60]
print('checked fourth-switch obstruction for', len(positive), 'remaining cases')
print(len(records), 'profiles and', sum(int(row[3]) for row in records), 'libraries')
