from itertools import combinations
from h5_three_sink_leak_sets import EDGES,N
covers={s for s in range(1024) if all(s&e for e in EDGES)}
assert min(s.bit_count() for s in covers)==6
minimum={s for s in covers if s.bit_count()==6}
assert len(minimum)==13 and len(N)==16 and len(EDGES)==13
for k in (1,2,3):
    xs=[s for s in range(1024) if s.bit_count()==k]
    ys=[s for s in range(1024) if s.bit_count()==6-k]
    partners={x:{y for y in ys if (x|y) in minimum} for x in xs}
    rectangles=[(a,b,c,d) for a,b in combinations(xs,2) if (a&b).bit_count()<=1
                for c,d in combinations(partners[a]&partners[b],2)
                if (c&d).bit_count()<=1]
    print(k,len(rectangles))
    assert not rectangles
