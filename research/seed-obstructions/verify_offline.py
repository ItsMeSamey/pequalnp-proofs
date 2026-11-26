"""Verify sample dominance forcing every four-point output to reject off-line pairs."""
from itertools import combinations
from pathlib import Path
from verify_packing import samples, require

rows, front, target = samples(Path(__file__).with_name('L-meta-18968.json'))
lines = range(6, 13)
neighborhoods = [sum(1 << ((line+d) % 13) for d in (0,1,3,9)) for line in lines]
for j, neighborhood in enumerate(neighborhoods):
    line_bit = 1 << (13+j)
    negatives = [row for i,row in enumerate(rows) if not target >> i & 1 and row & line_bit]
    points = [row & 8191 for i,row in enumerate(rows)
              if (target ^ front) >> i & 1 and row & (127 << 13) == line_bit]
    require(len(points) == 4 and all(p.bit_count() == 1 and p & neighborhood for p in points),
            'unexpected positive singleton')
    count = 0
    for a,b in combinations([i for i in range(13) if not neighborhood >> i & 1], 2):
        pair = (1 << a) | (1 << b)
        require(any(row & pair == pair and
                    any(all(s == neighborhood or not s & p or s & row for s in neighborhoods)
                        for p in points)
                    for row in negatives), 'missing dominance witness')
        count += 1
    print(j+6, count)
