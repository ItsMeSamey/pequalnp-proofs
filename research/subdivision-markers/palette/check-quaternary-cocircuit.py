from itertools import combinations,product
from random import Random
def mul(a,b):
    return ((a if b&1 else 0)^(((a<<1)^(7 if a&2 else 0)) if b&2 else 0))
points=list(product(range(4),repeat=2))
lines={frozenset(p for p in points if mul(a,p[0])^mul(b,p[1])==c) for a,b in points if a|b for c in range(4)}
assert len(lines)==20
assert not any(all(set(S)&L for L in lines) for S in combinations(points,6))
assert all({p for p in points if 0 in p}&L for L in lines)
def span(X):
    s={0}
    for x in X:s.update(x^y for y in tuple(s))
    return s
rng=Random(94776)
cases=0
for _ in range(120):
    E=rng.sample(range(32),rng.randrange(4,10))
    if len(span(e>>2 for e in E))!=8:continue
    old=any((span(S)&set(range(16)))=={0,4,8,12} for n in range(len(E)+1) for S in combinations(E,n))
    rhs=False
    for a,b,c in product(range(4),repeat=3):
        if any(s==v for s in (a,b) for v in (1,2,3)):continue
        good=[e>>2 for e in E if ((a if e&4 else 0)^(b if e&8 else 0)^(c if e&16 else 0))==e&3]
        rhs |= len(span(good))==8
    assert old==rhs
    cases+=1
print(cases,'transfer checks and all 8008 six-point patterns passed')
