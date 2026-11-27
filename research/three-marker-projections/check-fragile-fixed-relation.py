from collections import Counter
from itertools import combinations, combinations_with_replacement
def symp(x,y):
    return (((x>>3)&y)^((y>>3)&x)).bit_count()%2
def echelon(vectors):
    rows={}
    for v in vectors:
        while v and v.bit_length() in rows:v^=rows[v.bit_length()]
        if v:rows[v.bit_length()]=v
    return rows
def residual(v,rows):
    for p in sorted(rows,reverse=True):
        if v>>(p-1)&1:v^=rows[p]
    return v
def quadratic(f):
    return (1|(f<<1)) | sum((((f>>i)&(f>>j)&1)<<(9+k)) for k,(i,j) in enumerate(combinations(range(8),2)))
def fragile(f):
    return any((f>>z)&1 and all(not ((f>>(z^k))&1) for k in (1,2,4)) for z in range(8))
states={}
for a,b,c in combinations(range(1,64),3):
    if a^b==c or symp(a,b) or symp(a,c) or symp(b,c):continue
    L=frozenset((a,b,c,a^b,a^c,b^c,a^b^c))
    if L in states:continue
    f=sum((not any((x>>3)==(z&x) for x in L))<<z for z in range(8))
    states[L]=f
assert len(states)==135 and len(set(states.values()))==135
out=Counter()
for w in range(1,64):
    eligible=[L for L in states if w in L]
    assert len(eligible)==15
    yesmask=sum(fragile(states[L])<<i for i,L in enumerate(eligible))
    no=echelon([quadratic(0)]+[quadratic(states[L]) for i,L in enumerate(eligible) if not (yesmask>>i&1)])
    for i,L in enumerate(eligible):
        if yesmask>>i&1:assert residual(quadratic(states[L]),no)
    caps={sum(L.isdisjoint(C)<<i for i,L in enumerate(eligible)) for C in states}
    for c,d in combinations_with_replacement(caps,2):
        assert c&d==0 or c&d&~yesmask
    out[yesmask.bit_count()]+=1
assert out=={6:35,0:28}
print(len(states),'Lagrangians;',dict(out),'strata by accepting-state count')
