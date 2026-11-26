from itertools import combinations
from random import Random

def span(values):
    result = {0}
    for value in values:
        result.update(x ^ value for x in tuple(result))
    return frozenset(result)

U = span([1, 2, 4, 8])
H = span([1, 2])

def traces(columns, h=0):
    def quotient(x):
        return min(x, x ^ h)
    rows = [quotient(x) for x in columns]
    boundary = {quotient(x) for x in U}
    return {span(subset) & boundary for n in range(len(rows)+1)
            for subset in combinations(rows, n)}

def directional(columns):
    result = H
    for h in (1, 2, 3):
        image = frozenset(min(v, v ^ h) for v in H)
        if image not in traces(columns, h):
            result = result & {0,h}
    return result

def check(components):
    spaces = [directional(c) for c in components]
    local = [traces(c) for c in components]
    assert spaces == [span(v for K in choices if K <= H for v in K) for choices in local]
    decision = H in traces(sum(components, []))
    active = [i for i, S in enumerate(spaces) if len(S)>1]
    if span(v for S in spaces for v in S) != H:
        assert not decision
    elif len(active) >= 2:
        assert decision
    else:
        assert decision == (H in local[active[0]])

rng = Random(36960)
for case in range(160):
    check([[p^x for x in rng.sample(range(16),rng.randrange(2,6))] for p in (16,32)])
C = [16 ^ x for x in (0,1,4,6,8,12)]
assert directional(C)==H and H not in traces(C)
check([C])
print('161 controls passed')
