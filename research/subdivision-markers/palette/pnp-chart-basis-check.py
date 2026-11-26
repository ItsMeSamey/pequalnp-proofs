from itertools import combinations
from functools import reduce
from operator import xor
from random import Random

def span(values):
    space = {0}
    for v in values:
        space |= {v^x for x in space}
    return space

def tag(g,k,d):
    return reduce(xor, ((g>>(2*i))&3 for i in range(d) if k>>i&1), 0)

def check(E,d):
    canon={}
    for k,b,h in E:
        canon.setdefault((k,b),h)
    all_g=range(4**d)
    actual=any({x for x in span([(k<<4)^(b<<2)^h for k,b,h in E if tag(g,k,d)==b]) if x<16}==set(range(4)) for g in all_g)
    for pair in combinations(E,2):
        G=[g for g in all_g if all(tag(g,k,d)==b for k,b,h in pair)]
        if not G:continue
        offset=G[0]; free=[]; seen={0}
        for g in G:
            v=g^offset
            if v not in seen:
                free.append(v); seen|={x^v for x in seen}
        for s in range(min(4,len(free))+1):
            for z in combinations(free,s):
                g=reduce(xor,z,offset); residues=[]; sites=[]
                for k,b,h in pair:
                    sites.append((k<<4)^(b<<2)^h)
                    for i in range(d):
                        if k>>i&1:
                            t=tag(g,1<<i,d); u=canon[1<<i,t]; h^=u
                            sites.append((1<<(i+4))^(t<<2)^u)
                    residues.append(h)
                if len(span(residues))==4:
                    assert actual and {x for x in span(sites) if x<16}==set(range(4))
                    return True
    assert not actual
    return False

rng=Random(44258); outcomes=[]
for d in (2,3):
    for j in range(12):
        E=[(1<<i,b,rng.randrange(4)) for i in range(d) for b in range(4)]
        E += [(rng.randrange(1<<d),rng.randrange(4),rng.randrange(4)) for _ in range(7)]
        E += [(k,b,rng.randrange(4)) for k,b,h in rng.sample(E,3)]
        if j%3==0:E=[(k,b,h&1) for k,b,h in E]
        outcomes.append(check(E,d))
print(len(outcomes),'fixtures;',sum(outcomes),'YES;',len(outcomes)-sum(outcomes),'NO')
