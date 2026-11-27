"""Verify the B=25,N=2 exclusion on the pinned projected21 care data."""
from pathlib import Path
from functools import lru_cache
from itertools import combinations
import json
import runpy

here = Path(__file__).resolve().parent
checked = runpy.run_path(str(here / 'verify_projected27.py'))
care, bits = checked['care'], checked['bits']
outside = checked['outside']
general, monotone = checked['general'], checked['monotone']
# Colors 0..3 are interchangeable positive-path groups; 4 may have mixed signs.
families = [monotone]*4 + [general]
order = sorted(bits, key=lambda j: -sum(1/e.bit_count() for e in monotone+general if e & 1<<j))


def partitions(i, groups):
    if i == len(order):
        yield groups
        return
    bit = 1 << order[i]
    for k,g in enumerate(groups):
        if k < 4 and not g and 0 in groups[:k]:
            continue
        enlarged = g | bit
        if all(enlarged & e != e for e in families[k]):
            yield from partitions(i+1,groups[:k]+(enlarged,)+groups[k+1:])


def feasible(fibers):
    # Boolean implication graph. Use a bitset for the transitive closure.
    points = sorted({p for fiber in fibers for p,t in fiber})
    ids = {p:2*i for i,p in enumerate(points)}
    size = 2*len(points)
    reach = [1<<i for i in range(size)]

    def imply(a,b):
        reach[a] |= 1<<b
        reach[b^1] |= 1<<(a^1)

    for a,b in combinations(points,2):
        if a & b == a:
            imply(ids[a],ids[b])
    for fiber in fibers:
        for (a,s),(b,t) in combinations(fiber,2):
            if s != t:
                imply(ids[a],ids[b]^1)
                imply(ids[a]^1,ids[b])
    for j in range(size):
        bit = 1<<j
        for i in range(size):
            if reach[i] & bit:
                reach[i] |= reach[j]
    return all(not (reach[i] & (1<<(i+1)) and reach[i+1] & (1<<i)) for i in range(0,size,2))


@lru_cache(None)
def first_possible(group,upstream,negative):
    worlds = {}
    for pattern,label in care.items():
        external = pattern & ~group
        context = external & (outside|upstream)
        worlds.setdefault(context,{}).setdefault(external,[]).append(((pattern^negative)&group,label))
    return all(feasible(list(fibers.values())) for fibers in worlds.values())


def has_order(groups,upstream=0):
    if not groups:
        return True
    for i,(g,neg) in enumerate(groups):
        if first_possible(g,upstream,neg) and has_order(groups[:i]+groups[i+1:],upstream|g):
            return True
    return False


count = 0
for gs in partitions(0,(0,)*5):
    count += 1
    negative = gs[4]
    while True:
        colored = tuple((g, negative if i == 4 else 0) for i,g in enumerate(gs))
        if has_order(colored):
            raise ValueError('admissible signed group ordering',colored)
        if not negative:
            break
        negative = (negative-1) & gs[4]
if count != 66:
    raise ValueError('unexpected partition count',count)
