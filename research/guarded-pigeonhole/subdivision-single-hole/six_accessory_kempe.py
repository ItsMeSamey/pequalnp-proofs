"""Labeled greatest-fixed-point obstruction for the six-port accessory."""
from itertools import product,combinations
from collections import Counter
def orbit(s):
    d={}
    return ''.join(str(d.setdefault(x,1+len(d))) for x in s)
def match(P):
    if not P:yield ();return
    for j in range(1,len(P)):
        for other in match(P[1:j]+P[j+1:]):yield ((P[0],P[j]),)+other
def test(S,s):
    for i,j in combinations(range(3),2):
        active=tuple(p for p,c in enumerate(s) if c in (i,j))
        for edges in match(active):
            images={s}
            for u,v in edges:
                changed=set()
                for t in images:
                    z=list(t);z[u]=i+j-z[u];z[v]=i+j-z[v]
                    changed.add(tuple(z))
                images.update(changed)
            if images<=S:break
        else:return False
    return True
S={s for s in product(range(3),repeat=6)
   if all(s.count(c)%2==0 for c in range(3))
   and (Counter(s[:3])!=Counter(s[3:]) or (len(set(s[:3]))==3 and s[:3]==s[3:]))}
expected=[(96,16),(24,4),(6,1),(0,0)]
for n,k in expected:
    orbits={orbit(s) for s in S}
    assert (len(S),len(orbits))==(n,k)
    print(n,k,sorted(orbits))
    S={s for s in S if test(S,s)}
