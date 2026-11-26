"""Check outside-pair rejections for each noncanonical eight-wire family."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from verify_mixed import coords, front, target
base = Path(__file__).parent
can = [sum(1 << ((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
data = [coords(i) for i in range(676)]
relations = {(data[p][0],data[n][0]) for p in range(676) if (target^front)>>p&1
             for n in range(676) if not target>>n&1 and not data[p][1]&~data[n][1]}
pairs = [(1<<x)|(1<<y) for x,y in combinations(range(13),2)]
counts = Counter()
for row in (base/'families.txt').read_text().splitlines():
    family = list(map(int,row.split()))
    missing = set(can)-set(family)
    counts[len(missing)] += 1
    negatives = {m:set() for m in family}
    for a,b in relations:
        eligible = [m for m in family if m&a and not m&b]
        assert eligible
        if len(eligible) == 1:
            negatives[eligible[0]].add(b)
    parts = sorted(set(family)-set(can),key=int.bit_count)
    for t in can:
        if t in family:
            required = [t]
        elif len(missing)==1:
            assert len(parts)==2 and parts[0]|parts[1]==t
            required = parts
        else:
            q=parts[0]
            assert q.bit_count()==1 and q&t and (t^q) in parts
            required=[t^q]
        for s in required:
            assert all(any(not pair&~b for b in negatives[s])
                       for pair in pairs if not pair&t)
assert counts == {1:175,2:21,3:6}
print('Verified outside-pair rejections for 175, 21 and 6 families.')
