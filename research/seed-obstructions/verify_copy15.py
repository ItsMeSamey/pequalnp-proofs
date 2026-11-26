"""Check the six 8-point, 7-line families with a single extra edge."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import sys

base = Path(__file__).resolve().parent
sys.path.insert(0, str(base))
from verify_packing import samples

rows, front, target = samples(base / 'L-meta-18968.json')
stars = {sum(1 << ((6+j+d) % 13) for d in (0, 1, 3, 9)) for j in range(7)}
families = set()
for p in range(13):
    q = 1 << p
    for split in combinations([s for s in stars if s & q], 3):
        families.add(tuple(sorted((stars - set(split)) | {s ^ q for s in split} | {q})))
assert len(families) == 6

def verify(family):
    def project(r):
        return ((r >> 13) & 127) | sum(bool(r & m) << (7+j) for j,m in enumerate(family))
    pos = sorted({project(r) for i,r in enumerate(rows) if (target ^ front) >> i & 1})
    neg = sorted({project(r) for i,r in enumerate(rows) if not target >> i & 1})
    neg = [n for n in neg if all(n == m or n & ~m for m in neg)]
    width = len(neg)
    neg_mask = (1 << width) - 1
    full = (1 << (len(pos) * width)) - 1
    @lru_cache(None)
    def distinguishes(wire):
        p,n,_ = wire
        return sum((neg_mask ^ n) << (k * width) for k in range(len(pos)) if p >> k & 1)
    def atom(j):
        return (sum(((p >> j) & 1) << k for k,p in enumerate(pos)),
                sum(((n >> j) & 1) << k for k,n in enumerate(neg)), j >= 7)
    initial = tuple(sorted(map(atom, range(15))))
    states = {(initial, False)}
    for step in range(1, 16):
        following = set()
        for state,copied in states:
            for i,j in combinations(range(len(state)), 2):
                a,b = state[i],state[j]
                if a[2] == b[2] != 2:
                    continue
                rest = [x for k,x in enumerate(state) if k != i and k != j]
                owed = full
                for x in rest:
                    owed &= ~distinguishes(x)
                for p,n in ((a[0]&b[0],a[1]&b[1]), (a[0]|b[0],a[1]|b[1])):
                    merged = p,n,2
                    remaining = owed & ~distinguishes(merged)
                    new = rest + [merged]
                    if not remaining:
                        following.add((tuple(sorted(new)), copied))
                    if not copied:
                        for retained in (a,b):
                            if not remaining & ~distinguishes(retained):
                                following.add((tuple(sorted(new + [retained])), True))
        states = following
        if not states:
            print(family, 'extinct after', step, 'gates', flush=True)
            return
    raise AssertionError('surviving mixed circuit')
for family in sorted(families):
    verify(family)
