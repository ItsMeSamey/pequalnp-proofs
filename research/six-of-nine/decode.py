"""Emit off-pair witnesses, followed by constraints left by six canonical outputs."""
from itertools import combinations
from pathlib import Path
import sys

base = Path(sys.argv[1]) if len(sys.argv) == 2 else Path(__file__).resolve().parent.parent / 'seed-obstructions'
sys.path.insert(0, str(base))
from verify_packing import samples, require

rows, front, target = samples(base / 'L-meta-18968.json')
targets = [sum(1 << ((j+d)%13) for d in (0,1,3,9)) for j in range(6,13)]
positive = [(row & 8191, row >> 13 & 127) for i,row in enumerate(rows) if (target ^ front) >> i & 1]
negative = [(row & 8191, row >> 13 & 127) for i,row in enumerate(rows) if not target >> i & 1]

def emit(pairs):
    print(len(pairs), *(x for pair in sorted(pairs) for x in pair))

for j, neighborhood in enumerate(targets):
    points = [p for p,lines in positive if lines == 1 << j]
    require(len(points) == 4 and all(p.bit_count() == 1 and p & neighborhood for p in points),
            'unexpected positive points')
    outside = [i for i in range(13) if not neighborhood >> i & 1]
    for a,b in combinations(outside,2):
        pair = (1 << a) | (1 << b)
        emit({(p,n) for p in points for n,lines in negative if not pair & ~n and lines >> j & 1
              and all(S == neighborhood or not S & p or S & n for S in targets)})
for j, omitted in enumerate(targets):
    fixed = targets[:j] + targets[j+1:]
    pairs = {(p,n) for p,l in positive for n,k in negative if not l & ~k and
             all(not S & p or S & n for S in fixed)}
    emit({(p,n) for p,n in pairs if not any(p == q and n != m and not n & ~m for q,m in pairs)})
print(*targets)
