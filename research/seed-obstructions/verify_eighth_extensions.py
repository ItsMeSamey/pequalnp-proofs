"""Additional sampled negative extensions for the eighth line signal."""
from itertools import combinations, combinations_with_replacement

from verify_mixed import coords, target

stars = [sum(1 << ((6+j+d) % 13) for d in (0, 1, 3, 9)) for j in range(7)]
negatives = sorted({coords(i) for i in range(676) if not (target >> i & 1)})
for j,star in enumerate(stars):
    for p in range(13):
        if not (star >> p & 1):
            assert any(lines >> j & 1 and points >> p & 1 for points,lines in negatives)
checked = 0
for j,star in enumerate(stars):
    for first,second in combinations_with_replacement([k for k in range(7) if k != j],2):
        eligible = [points for points,lines in negatives if lines >> j & 1
                    and points & stars[first] and points & stars[second]]
        for x,y in combinations([p for p in range(13) if not star >> p & 1],2):
            pair = (1 << x) | (1 << y)
            assert any(not pair & ~q for q in eligible), (j,first,second,x,y)
            checked += 1
assert checked == 5292
print("Verified all 5,292 outside-pair extensions meeting two specified other lines.")

concurrent = [c for c in range(13) if sum(bool(star & (1<<c)) for star in stars) >= 2]
punctured = 0
for c in concurrent:
    for j,star in enumerate(stars):
        for i,first in enumerate(stars):
            for k,second in enumerate(stars):
                if j in (i,k):
                    continue
                # The second guard is full whenever T does not contain c.
                other = second & ~(1<<c) if star & (1<<c) else second
                eligible = [q for q,lines in negatives if lines >> j & 1
                            and q & (first & ~(1<<c)) and q & other]
                for x,y in combinations([p for p in range(13) if not star >> p & 1], 2):
                    pair = (1<<x) | (1<<y)
                    assert any(not pair & ~q for q in eligible), (c,j,i,k,x,y)
                    punctured += 1
print("Verified",punctured,"outside-pair extensions with punctured guards.")
