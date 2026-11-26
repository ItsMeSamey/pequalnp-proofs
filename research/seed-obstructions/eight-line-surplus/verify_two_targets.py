"""Verify the four-leaf cofactor replacements without an external reachability table."""
from itertools import combinations,product
from collections import defaultdict
from joint import check

def possible_minimal(f):
    return [s for s in range(16) if f>>s&1 and all(not f>>(s^(1<<i))&1 for i in range(4) if s>>i&1)]
def options(a,b):
    minima=possible_minimal(a&~b)
    return [subset for k in range(1,min(3,len(minima))+1) for subset in combinations(minima,k)
            if all(not b>>(x|y)&1 for x,y in combinations(subset,2))]
def reachable():
    raw=tuple(sum(1<<j for j in range(16) if j>>i&1) for i in range(4))
    states={frozenset([0,65535,*raw])}
    result=defaultdict(set)
    for depth in range(5):
        nextstates=set()
        for state in states:
            for x in state:result[x].update(state)
            for a,b in combinations(state,2):
                for new in (a&b,a|b):
                    if new in state:continue
                    result[new].update(state|{new})
                    for old in state:result[old].add(new)
                    if depth<4:nextstates.add(state|{new})
        states=nextstates
    return result
if __name__=='__main__':
    for b in range(4):
        assert not check(b)
    hard=check(4);assert len(hard)==48
    reach=reachable();total=0
    for a,b in sorted(hard):
        for A,B,c in product(options(a,b),options(b,a),possible_minimal(a&b)):
            total+=1
            assert any(not (s&~a or t&~b) and all(s>>z&1 for z in (*A,c)) and
                       all(t>>z&1 for z in (*B,c)) for s,rr in reach.items()
                       for t in rr if not s&~a)
    assert total==120
    print('All 120 necessary positive configurations admit lower replacements in five gates.')
