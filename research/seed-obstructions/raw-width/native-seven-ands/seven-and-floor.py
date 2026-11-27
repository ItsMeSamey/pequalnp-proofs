"""Recompute just the singleton and foreign-private certificates from native.in."""
from pathlib import Path
from itertools import combinations
data=Path('/workspace/scratch/synthesis_new/native-seven-and-cuts/native.in')
rows=[tuple(map(int,line.split())) for line in data.read_text().splitlines()]
k,l=rows[0]
edges=[p|(t<<13) for p,t in rows[1:k+1]]
negative=[p|(t<<13) for p,t in rows[k+1:]]
assert len(negative)==l
def cert(q):
    forbidden=q
    for e in edges:
        if q&e: forbidden|=e
    remain=[e for e in edges if not e&forbidden]
    live=0
    for e in remain:live|=e
    choices=set()
    for tagmask in range(128):
        t=(tagmask<<13)&live
        excluded=0
        for e in remain:
            if e&t:excluded|=e
        choices.add(t|((live&8191)&~excluded))
    maximal=[a for a in choices if not any(a!=b and a&~b==0 for b in choices)]
    forced=set()
    for n in negative:
        if q&~n:continue
        compatible=[a for a in maximal if not n&live&~a]
        if len(compatible)==1:forced.add(compatible[0])
    return len(forced)
for i in range(13):
    d=sum(bool(e&(1<<i)) for e in edges)
    s=cert(1<<i)
    assert 7-(s-1).bit_length()==d
private=[1<<i for i in range(13) if sum(bool(e&(1<<i)) for e in edges)==1]
cross=[cert(p|t) for p in private for t in [1<<j for j in range(13,20)] if p|t not in edges]
assert sorted(set(cross))==[17,20] and len(cross)==24
assert all(any((a|b)&~n==0 for n in negative) for a,b in combinations([1<<i for i in range(13)],2))
print('13 singleton caps equal degrees; 24 cross floors; 78 distinct point pairs covered')
