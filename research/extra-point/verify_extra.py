"""Check which canonical outputs can lose an off-neighborhood pair witness."""
import sys
from collections import Counter
from itertools import combinations
from pathlib import Path

base = Path(__file__).resolve().parent.parent / 'seed-obstructions'
if len(sys.argv) == 2:
    base = Path(sys.argv[1])
sys.path.insert(0, str(base))
from verify_packing import samples, require

rows, front, target = samples(base / 'L-meta-18968.json')
mask = (1 << 13) - 1
targets = [sum(1 << ((j+d) % 13) for d in (0, 1, 3, 9)) for j in range(6, 13)]
negative = [(r & mask, (r >> 13) & 127) for i, r in enumerate(rows) if not target >> i & 1]
positive = [(r & mask, (r >> 13) & 127) for i, r in enumerate(rows) if (target ^ front) >> i & 1]
bad = [set() for _ in targets]
for j, neighborhood in enumerate(targets):
    points = [p for p, lines in positive if lines == 1 << j]
    require(len(points) == 4 and set(points) == {1<<i for i in range(13) if neighborhood>>i & 1},
            'unexpected positive rows')
    for a,b in combinations([i for i in range(13) if not neighborhood >> i & 1], 2):
        pair = (1 << a) | (1 << b)
        required, forbidden = 0, 0
        for n, lines in negative:
            if pair & ~n or not lines >> j & 1:
                continue
            for p in points:
                if all(S == neighborhood or not S & p or S & n for S in targets):
                    required |= p
                    forbidden |= n
        require(required != 0, 'no canonical witness')
        if required & forbidden:
            continue
        free = mask & ~(required | forbidden)
        sub = free
        while True:
            bad[j].add(required | sub)
            if not sub:
                break
            sub = (sub - 1) & free
hist = Counter(sum(H in choices for choices in bad) for H in range(1 << 13))
require(hist == {0: 8122, 1: 70}, 'unexpected witness histogram')
print('potentially unsafe signatures per target:', [len(choices) for choices in bad])
print('numbers of additional signatures allowing 0 or 1 potentially unsafe targets:', hist[0], hist[1])
