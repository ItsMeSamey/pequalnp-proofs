"""Exclude mixed read-once trees for the 27 eight-point-signature split families."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import sys

if not Path(__file__).with_name("verify_mixed.py").exists():
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "synthesis_new/mixed"))
from verify_mixed import coords, target, front

stars = {sum(1 << ((6+j+d) % 13) for d in (0, 1, 3, 9)) for j in range(7)}
families = set()
for p in range(13):
    point = 1 << p
    hits = sorted(star for star in stars if point & star)
    for nsplit in range(2, len(hits)+1):
        for split in combinations(hits, nsplit):
            masks = (stars-set(split)) | {star ^ point for star in split} | {point}
            families.add(tuple(sorted(masks)))
assert len(families) == 27

positives = sorted({coords(i) for i in range(676) if (target ^ front) >> i & 1})
negatives = {coords(i) for i in range(676) if not (target >> i & 1)}
negatives = sorted((p,l) for p,l in negatives if not any(
    (p,l) != (q,m) and not (p & ~q or l & ~m) for q,m in negatives))
width = len(negatives)
neg_mask = (1 << width)-1
obligations = (1 << (width*len(positives)))-1

@lru_cache(None)
def distinguishes(wire):
    positive, negative, _ = wire
    return sum((neg_mask ^ negative) << (width*i)
               for i in range(len(positives)) if positive >> i & 1)

def atom(side, mask):
    def column(rows):
        return sum(bool(row[side] & mask) << i for i,row in enumerate(rows))
    return column(positives), column(negatives), side

def check(family):
    # Side 0 denotes point, side 1 line, and side 2 mixed ancestry.
    leaves = [atom(0, mask) for mask in family] + [atom(1, 1<<i) for i in range(7)]
    seen = set()
    def visit(state):
        if state in seen:
            return False
        seen.add(state)
        if len(state) == 1:
            return True
        for i,j in combinations(range(len(state)), 2):
            a,b = state[i],state[j]
            if a[2] == b[2] != 2:
                continue
            rest = [w for k,w in enumerate(state) if k not in (i,j)]
            uncovered = obligations
            for w in rest:
                uncovered &= ~distinguishes(w)
            for pos,neg in ((a[0]&b[0],a[1]&b[1]), (a[0]|b[0],a[1]|b[1])):
                wire = pos,neg,2
                if uncovered & ~distinguishes(wire):
                    continue
                if visit(tuple(sorted(rest+[wire]))):
                    return True
        return False
    assert not visit(tuple(sorted(leaves))), "found a separating tree"
    return len(seen)

if __name__ == "__main__":
    counts = Counter(check(family) for family in sorted(families))
    assert counts == {52:6, 203:21}, counts
    print("All 27 families excluded:", sorted(counts.items()), "states per family/count.")
