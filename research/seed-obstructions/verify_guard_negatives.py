"""Verify the sampled negative extensions used to remove shared point guards."""
from itertools import combinations
from pathlib import Path
import sys

if not Path(__file__).with_name("verify_mixed.py").exists():
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "synthesis_new/mixed"))
from verify_mixed import coords, target

stars = [sum(1 << ((6+j+d) % 13) for d in (0, 1, 3, 9)) for j in range(7)]
negatives = sorted({coords(i) for i in range(676) if not (target >> i & 1)})
assert all(any(q & (1 << p) for q,_ in negatives) for p in range(13))
checked = 0
for j,star in enumerate(stars):
    for k,other in enumerate(stars):
        if k == j:
            continue
        assert (star & other).bit_count() == 1
        eligible = [q for q,lines in negatives if lines >> j & 1 and q & other]
        for x,y in combinations([p for p in range(13) if not star >> p & 1], 2):
            pair = (1 << x) | (1 << y)
            assert any(not (pair & ~q) for q in eligible), (j,k,x,y)
            checked += 1
assert checked == 1512
print("Verified all 1,512 outside-pair extensions for the 42 ordered line pairs.")
