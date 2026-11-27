from collections import Counter
from itertools import combinations, product

universe = set(range(16))
def full(points):
    base = min(points)
    span = {0}
    for value in points:
        span |= {x ^ value ^ base for x in span}
    return len(span) == 16

def apply(x, h):
    return (x % 4 if h & 1 else 0) ^ (x // 4 if h & 2 else 0)

def transpose(x):
    return (x & 9) | ((x & 2) << 1) | ((x & 4) >> 1)

simplex = {0, 1, 2, 4, 8}
linear_tests = [{x for x in universe if apply(transpose(x) if t else x, h) == v}
                for t,h,v in product(range(2), range(1,4), range(4))]
invertible = {x for x in universe if len({0,x%4,x//4}) == 3}
tests = linear_tests + [{x ^ l for x in invertible} for l in universe]
sizes, remainder = Counter(), Counter()
for candidate in combinations(universe,5):
    s = set(candidate)
    if not full(s):
        continue
    n = len({a ^ b for a,b in product(simplex,s)})
    sizes[n] += 1
    if n == 11:
        assert any(s == {a ^ v for a in simplex} for v in universe)
    covered = set().union(*(t for t in tests if not s & t))
    remainder[len(universe - s - covered)] += 1
assert sizes == {11:16,13:480,14:960,15:1152,16:80}
assert remainder == {0:1872,1:816}
print(sizes, remainder)
