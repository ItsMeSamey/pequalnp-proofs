from pathlib import Path
from itertools import permutations,product
from functools import reduce
from operator import or_
E=[sum(1<<int(i) for i in e) for e in '12 34 04 05 16 27 38 49 57 79 69 68 58'.split()]
I=[v for v in range(1024) if all(v&e!=e for e in E) and all(any(e&~(v|1<<i)==0 for e in E) for i in range(10) if v>>i&1==0)]
raw=[sum(1<<j for j,x in enumerate(E+I) if x>>i&1) for i in range(10)]
directions=[(a,b,z) for a,b in product(range(2),repeat=2) for z in (range(2) if a or b else (None,))]
arms=[{i for i,d in enumerate(directions) if d[axis]==side} for axis,side in product(range(3),range(2))]
def check(h,q):
    fs=raw+[h,q]
    rows=[sum(1<<j for j,f in enumerate(fs) if f>>i&1) for i in range(29)]
    es,ns=rows[:13],rows[13:]
    groups=[]
    for i in range(16):
        g={j for j in range(16) if all(e&~(ns[i]|ns[j]) for e in es)}
        if g not in groups:groups.append(g)
    assert len(groups)==7 and sum(map(len,groups))==16 and set.union(*groups)==set(range(16))
    bans=[reduce(or_,(ns[j] for j in g)) for g in groups]
    assert all(all(e&~u for e in es) for u in bans)
    for layout in permutations(bans):
        clauses=[0]*7
        for arm in arms:
            forbidden=reduce(or_,(layout[i] for i in arm))
            for i in arm:clauses[i]|=(4095^forbidden)
        assert any(not(e&cl) for e in es for cl in clauses)
    print(h,q,sorted(map(len,groups)),5040)
for line in Path(__file__).with_name('two_prefix.log').open():
    if line.startswith('survivor'):check(*map(int,line.split()[2:]))
