"""Replay every observed augment, including matching uniqueness on extended paths."""
from functools import lru_cache
from inspect import getsourcelines
from random import Random
import sys

import gim_binary_parity as gim
from symmetric_syndrome import invertible

rng = Random(50173)
stats = dict(aug=0, with_transform=0, bud=0, coalesce=0, largest_path=0, cases=0)
source, start = getsourcelines(gim.search)
line = lambda needle: start + next(i for i,s in enumerate(source) if needle in s)
marks = {line("return sum("): "aug", line("t=transform(p,q)"): "bud",
         line("group_new=set(group[b])"): "coalesce"}

def local(frame,event,arg):
    if event != "line" or frame.f_lineno not in marks:
        return local
    event = marks[frame.f_lineno]
    stats[event] += 1
    if event != "aug":
        return local
    loc = frame.f_locals
    path, rows, orig = (loc[x] for x in ("path","rows","originals"))
    mapped = [orig[i] for i in path]
    stats["largest_path"] = max(stats["largest_path"],len(path))
    stats["with_transform"] += any(i >= loc["n"] for i in path)
    assert len(set(mapped)) == len(path) and len(path)%2==0
    assert mapped[0]//2 != mapped[-1]//2
    assert all((mapped[i]^1)==mapped[i+1] for i in range(1,len(path)-1,2))
    assert not set(mapped[1:-1]).intersection(loc["sources"])
    assert all(rows[path[i]] >> path[i+1] & 1 for i in range(0,len(path),2))
    @lru_cache(None)
    def matchings(mask):
        if not mask:
            return 1
        first = mask & -mask
        left = mask ^ first
        total = 0
        for j in gim.bits(rows[first.bit_length()-1] & left):
            total += matchings(left ^ (1<<j))
            if total > 1:
                return 2
        return total
    assert matchings(sum(1<<i for i in path))==1
    return local

def trace(frame,event,arg):
    return local if frame.f_code is gim.search.__code__ else None

sys.settrace(trace)
for n in (6,10,14,18,24):
    for k in range(75):
        rows = [0]*n
        for i in range(n):
            for j in range(i):
                if rng.randrange(100)<(10,22,40,65)[k%4]:
                    rows[i] |= 1<<j
                    rows[j] |= 1<<i
        twist = rng.getrandbits(n)
        if k%3==0:
            twist = 1 | (1<<(n-2))
        ans = gim.solve(rows,twist)
        def feasible(s):
            support = twist^s
            return invertible([rows[i]&support for i in gim.bits(support)])
        if ans is not None:
            assert feasible(ans) and all((ans>>(i&~1)&3) in (0,3) for i in range(n))
        elif n<=18:
            assert not any(feasible(sum(3<<(2*i) for i in gim.bits(s)))
                           for s in range(1<<(n//2)))
        stats["cases"]+=1
sys.settrace(None)
print(stats)
