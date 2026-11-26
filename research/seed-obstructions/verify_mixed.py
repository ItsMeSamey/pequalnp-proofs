import json
from itertools import combinations
from pathlib import Path
from verify_packing import samples
base=Path(__file__).parent
rows,front,target=samples(base/'L-meta-18968.json')
sets=json.loads((base/'pairs.json').read_text())
def coords(index):
    return rows[index]&8191,(rows[index]>>13)&127
for name,i in [('point',0),('line',1)]:
    pairs=[(coords(p),coords(n)) for p,n in sets[name]]
    assert len(pairs)==7
    for (p,n),(pi,ni) in zip(pairs,sets[name]):
        assert ((target^front)>>pi)&1 and not (target>>ni)&1
        assert p[i]&~n[i] and not p[1-i]&~n[1-i]
    for (p,n),(q,m) in combinations(pairs,2):
        assert not p[i]&~m[i] or not q[i]&~n[i]
for k in range(676):
    p,l=coords(k)
    value=any(l>>j&1 and any(p>>((6+j+d)%13)&1 for d in [0,1,3,9]) for j in range(7))
    assert value==bool((target^front)>>k&1)
print('Seven point-exclusive pairs and seven line-exclusive pairs verified.')
print('The minimum is 13 mixed gates with all monotone one-side signals free.')
