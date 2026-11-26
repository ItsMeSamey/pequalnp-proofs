from random import Random
from itertools import product
from collections import Counter
rng=Random(478)
def span(cols):
    U={0}
    for x in cols:U|={u^x for u in U}
    return U
def pf(rows,v):
    w=0
    for r,x in enumerate(rows):
        if (x&v).bit_count()%2:w^=1<<r
    return w
def linear(tag,w):
    return (tag[0] if w&1 else 0)^(tag[1] if w&2 else 0)
def xor(values):
    r=0
    for x in values:r^=x
    return r
totals=Counter()
for _ in range(160):
    R=rng.randrange(2,9)
    N=rng.randrange(1,7)
    # First two port covectors are coordinate-dual to u1,u2. q0 is the only chord meeting these rows.
    P=[1,2]+[rng.randrange(4) for r in range(R-2)]
    H=[3^(rng.randrange(1<<(R-2))<<2)]+[(rng.randrange(1<<(R-2))<<2) for _ in range(N-1)]
    cols=[1<<i for i in range(R)]+H
    tags=[(rng.randrange(8),rng.randrange(8)) for c in cols]
    chordfix=[rng.randrange(1,4) for q in H[1:]]
    ums=[pf(P,w) for w in range(4)]
    colors={}
    scores={}
    for x,y,z in product(range(4),repeat=3): # independent proxy colors w1,w2,w3
        s1,s2=x^z,y^z
        ch=[z]+chordfix
        basis=[(s1 if a&1 else 0)^(s2 if a&2 else 0)^xor(v for c,v in zip(H,ch) if c>>i&1) for i,a in enumerate(P)]
        w=basis+ch
        assert w[0]==x and w[1]==y
        Z=[c for c,v in zip(cols,w) if not v]
        PZ=[a for a,v in zip((1,2,3),(x,y,z)) if not v]
        if len(span(PZ))==1<<len(PZ):
            assert len(span(Z))==1<<len(Z)
            assert all(a in span(PZ) for a in range(4) if ums[a] in span(Z))
            totals['admissible_lifts']+=1
        if all((x,y,z)):
            assert all(a==0 for a in range(4) if ums[a] in span(Z))
            colors[s1,s2]=w
        scores[(x,y,z)]=xor(linear(t,v) for t,v in zip(tags,w))
    assert len(colors)==16
    bias=scores[(0,0,0)]
    T=[]
    for i in range(3):
        cs=[]
        for v in (1,2):
            x=[0]*3;x[i]=v
            cs.append(scores[tuple(x)]^bias)
        T.append(tuple(cs))
    for w,t in scores.items():assert bias^xor(linear(tg,v) for tg,v in zip(T,w))==t
    totals['fully_covered_imbalances']+=len(colors)
    totals['affine_tag_cases']+=len(scores)
print(dict(totals))
