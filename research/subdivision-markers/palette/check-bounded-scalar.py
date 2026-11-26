from itertools import combinations,product
from random import Random
def sp(xs):
    s={0}
    for x in xs:s.update(x^y for y in tuple(s))
    return s
def family(E,b):
    out=set()
    for phi in (0,4,8,12):
        bad=frozenset(i for i,(v,o) in enumerate(E) if ((v&phi).bit_count()&1)!=((o>>b)&1))
        if len(sp(v for i,(v,o) in enumerate(E) if i not in bad))==16:out.add(bad)
    return out
def enumeration(F):
    seen=[]
    while True:
        candidate=next((C for choices in product(*seen) for C in F if C.isdisjoint(choices)),None)
        if candidate is None:return set(seen)
        assert candidate not in seen
        seen.append(candidate)
rng=Random(9913)
for _ in range(150):
    E=[(rng.randrange(16),rng.randrange(4)) for i in range(8)]
    families=[family(E,b) for b in (0,1)]
    assert all(enumeration(F)==F for F in families)
    joint=any(len(sp(v for i,(v,o) in enumerate(E) if i not in F|G))==16 for F,G in product(*families))
    U={h|(o<<4) for h in range(4) for o in range(4)}
    direct=any(sp(v|(o<<4) for v,o in C)&U==set(range(4)) for n in range(9) for C in combinations(E,n))
    if len(sp(v>>2 for v,o in E))==4:assert direct==joint
print('150 scalar chart/transversal controls passed')
