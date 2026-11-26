from random import Random
from functools import reduce
from operator import xor
rng=Random(73)
def supports(g):
    return [x for x in range(1<<len(g)) if all(not(x>>i&1 and (x&n).bit_count()%2) for i,n in enumerate(g))]
def score(x,w):
    return reduce(xor,(s for i,s in enumerate(w) if x>>i&1),0)
def graph(n,edges):
    g=[0]*n
    for i,j in edges:
        g[i]|=1<<j
        g[j]|=1<<i
    return g
for trial in range(100):
    n=6
    edges=[(i,j) for i in range(3) for j in range(3,6) if rng.randrange(2)]
    p=[i for i in range(3) if rng.randrange(2)]
    q=[i for i in range(3,6) if rng.randrange(2)]
    # private path l,a,b,r. l touches q; r touches p
    full=graph(10,edges+[(6,7),(7,8),(8,9)]+[(6,j) for j in q]+[(9,i) for i in p])
    merged=graph(7,edges+[(6,j) for j in q+p])
    w=[rng.randrange(8) for _ in full]
    direct={score(x,w) for x in supports(full) if (x>>6^x>>9)&1==0}
    bare={score(x,w[:n]) for x in supports(graph(n,edges))}
    off=bare|{z^w[7] for z in bare}|{z^w[8] for z in bare}
    w2=w[:n]+[w[7]^w[6]^w[9]]
    for j in q: w2[j]^=w[7]^w[8]
    rec={score(x,w2)^w[7] for x in supports(merged)}
    assert direct==off|rec
for trial in range(1000):
    S=[{rng.randrange(8) for _ in range(6)} for _ in range(3)]
    e=[rng.randrange(8) for _ in S]
    def ask(offset,z):
        return any(z^a in s for a,s in zip(offset,S))
    for z in range(8):
        if ask(e,z): continue
        for m,s in enumerate(S):
            assert {k for k in range(8) if ask(e[:m]+[k^z]+e[m+1:],z)}==s
print('100 weighted graphs, 800 targets; 1000 conditional tables, 8000 targets')
