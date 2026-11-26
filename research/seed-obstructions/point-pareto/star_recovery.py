"""Minimum OR cost for a bank from which each star can be recovered by unions."""
from pathlib import Path
import sys
from input import point_obligations

free, rows = point_obligations(Path(sys.argv[1]))
stars = [sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
assert all((a & t).bit_count() <= 1 for a in free for t in stars)
best = {}
for raw in range(8192):
    local = {raw.bit_count(): 0}
    for t in stars:
        missing = (t & ~raw).bit_count()
        if not missing:
            continue
        following = {}
        for width, cost in local.items():
            for outputs in range(1, missing + 1):
                w = width + outputs
                if w <= 13:
                    c = cost + max(outputs, missing - outputs)
                    following[w] = min(following.get(w, c), c)
        local = following
    for width, cost in local.items():
        best[width] = min(best.get(width, cost), cost)
for width in range(7,14):
    print(width, min(cost for w,cost in best.items() if w<=width))
assert [best[w] for w in range(7,14)] == [21,18,15,12,9,5,0]

# One eleven-wire witness with nine actual binary OR gates.
selected = 964
boundary = [1<<i for i in range(13) if selected>>i&1]
available = {1<<i for i in range(13)}
gates = []
for star in stars:
    points = [1<<j for j in range(13) if star & ~selected & (1<<j)]
    if not points:
        continue
    total = points[0]
    for bit in points[1:]:
        assert total in available and bit in available
        gates.append((total,bit))
        total |= bit
        available.add(total)
    boundary.append(total)
assert len(boundary) == 11 and len(gates) == 9
assert all(any((b & p) and not b & n for b in boundary) for p,n in rows)
print('width-eleven point witness', boundary)
print('OR operands given by their masks', gates)
