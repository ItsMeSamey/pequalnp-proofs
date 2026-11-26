"""Independently compare coefficient-relation palettes with every physical selection."""
from itertools import product
from random import Random

def span(gens):
    s={0}
    for g in gens: s|={x^g for x in s}
    return frozenset(s)
def named(x,P):
    v=0
    for i,p in enumerate(P):
        if x>>i&1: v^=p
    return v
def relation(P,S):
    return frozenset((x<<2)|o for x in range(8) for o in range(4) if (named(x,P)<<2|o) in S)
def palette(E,P):
    seeds={frozenset({0})}
    for v in E:
        seeds|={frozenset(s|{x^v for x in s}) for s in seeds}
    return {relation(P,s) for s in seeds}
def merge(R,S):
    return frozenset((x&~3)|((x^y)&3) for x in R for y in S if x>>2==y>>2)
def probe(R,g,rogue):
    rel=frozenset((x<<2)|o for x in range(4) for o in range(4)
                  if ((x<<2)|o) in R or (rogue and (((x|4)<<2)|(o^g)) in R))
    if len(rel)!=4 or any(v in rel for v in (1,2,3)):return None
    return tuple(next(x&3 for x in rel if x>>2==bit) for bit in (1,2))
def check(parts,names,g):
    offset=0; E=[]; P=[0]*3
    R={frozenset(x<<2 for x in range(8))}
    for (dim,cols),pins in zip(parts,names):
        R={merge(a,b) for a in R for b in palette(cols,pins)}
        for j,v in enumerate(pins):P[j]^=v<<offset
        E.extend(((v>>2)<<(offset+2))|(v&3) for v in cols)
        offset+=dim
    assert R==palette(E,P)
    for rogue in (0,1):
        obtained={probe(r,g,use) for r in R for use in range(rogue+1)}-{None}
        cols=E+[(P[2]<<2)|g]*rogue
        actual=set()
        for mask in range(1<<len(cols)):
            S=span(v for i,v in enumerate(cols) if mask>>i&1)
            if len(S)==1<<offset and all(t not in S for t in (1,2,3)):
                pair=tuple(next(t for t in range(4) if (p<<2|t) in S) for p in P[:2])
                actual.add(pair)
        assert actual==obtained,(parts,names,g,rogue,actual,obtained)
    return len(R)

if __name__=='__main__':
    rng=Random(1401)
    total=0
    for _ in range(120):
        ds=[rng.randint(1,2),rng.randint(1,2),rng.randrange(2)]
        parts=[];names=[]
        for d in ds:
            cols=[(1<<(i+2))|rng.randrange(4) for i in range(d)]
            cols += [rng.randrange(1<<(d+2)) for j in range(rng.randrange(3))]
            parts.append((d,cols))
            names.append([rng.randrange(1<<d) for _ in range(3)])
        total+=check(parts,names,rng.randrange(4))
    print('120 independent planted direct sums;',total,'distinct palette entries checked against raw subsets, with and without rogue')
