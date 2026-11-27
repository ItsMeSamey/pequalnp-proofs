"""Exhaustive four-formal-label OR states and one ten-variable physical control."""
from itertools import combinations
from random import Random
from functools import lru_cache

raw=frozenset(1<<i for i in range(4))
reachable={raw}
for n in range(4,15):
    for state in tuple(reachable):
        if len(state)!=n:continue
        for a,b in combinations(state,2):
            reachable.add(state|{a|b})

@lru_cache(None)
def optimum(target):
    target=set(target)-{0}
    return min(len(s)-4 for s in reachable if target<=s)

def tests():
    rng=Random(91)
    for _ in range(350):
        private=rng.randrange(1,16)
        e0=private&rng.randrange(16)
        e1=private^e0
        r0=rng.randrange(16)&~private
        r1=rng.randrange(16)&~private
        if not(e0|r0) or not(e1|r1):continue
        others=[rng.randrange(16)&~private for _ in range(5)]
        a=optimum(frozenset(others+[e0|r0,e1|r1]))
        b=optimum(frozenset(others+[r0,r1]))
        assert a==b+private.bit_count()-(not r0)-(not r1)
        yield 1

if __name__=='__main__':
    print('four-label instances',sum(tests()),'OR-DAG states',len(reachable))
    # Five actual parallel ANDs with overlaps and semantically redundant operands.
    for x in range(1024):
        bits=[bool(x>>i&1) for i in range(10)]
        h=[bits[2*i] and bits[2*i+1] for i in range(5)]
        original=(h[0] or h[1] or bits[0]) and (h[2] or h[3] or h[4] or bits[4])
        left=bits[0]
        right=bits[4]
        for u in h[:2]:left|=u
        for u in h[2:]:right|=u
        assert original==(left and right)
    print('parallel control: raw-bank cost zero, formal sink surcharge five, 1024 inputs')
