"""Count omission sets retaining all three sufficient conditions for the 18-gate proof."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import runpy

data = runpy.run_path(str(Path(__file__).with_name('check-fano-almost-full-forks.py')))
rows = data['neg']
edges = data['flags']
requirements = list(data['swaps'].values())
for x in range(12):
    for y in range(12):
        pair = (1 << x) | (1 << y)
        if (x < 6) == (y < 6) or pair in edges:
            continue
        requirements.append(sum(1 << i for i, n in enumerate(rows) if not pair & ~n))
        requirements.append(sum(
            1 << i for i, n in enumerate(rows)
            if n >> x & 1 and any(n & (e ^ (1 << y)) for e in edges if e >> y & 1)
        ))
for k, expected in enumerate((1,21,198,1062,3441)):
    count = 0
    for removed in combinations(range(21),k):
        mask = sum(1 << i for i in removed)
        count += all(w & ~mask for w in requirements)
    assert count == expected
    print(k, count)
