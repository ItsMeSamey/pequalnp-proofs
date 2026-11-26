"""Read the pinned parent statement and emit the residual matrix for verify.cpp."""
import sys
from pathlib import Path

source = Path(__file__).resolve().parent.parent / 'seed-obstructions'
# The optional argument allows replay from a standalone checkout of this folder.
if len(sys.argv) == 2:
    source = Path(sys.argv[1])
sys.path.insert(0, str(source))
from verify_packing import samples, require

rows, front, target = samples(source / 'L-meta-18968.json')
mask = (1 << 38) - 1
require(front & ~target == 0, 'front outside target')
positive = {row & mask for i, row in enumerate(rows) if (target ^ front) >> i & 1}
negative = {row & mask for i, row in enumerate(rows) if not (target >> i & 1)}
negative = {n for n in negative if not any(n != m and not n & ~m for m in negative)}
require(all(row >> 38 == 0 for i, row in enumerate(rows) if (target ^ front) >> i & 1),
        'omitted signal positive on a required row')
require(all(any(not (row & mask) & ~n for n in negative)
            for i, row in enumerate(rows) if front >> i & 1), 'undominated erased row')
require((len(positive), len(negative)) == (28, 245), 'unexpected matrix dimensions')
differences = {p & ~n for p in positive for n in negative}
minimal = {d for d in differences if not any(d != e and not e & ~d for e in differences)}
expected = {1 << i for i in range(20) if i != 1} | {2 | (1 << j) for j in (20, 21, 31)}
require(minimal == expected, 'unexpected mandatory support conditions')
print(len(positive), len(negative), *sorted(positive), *sorted(negative))
