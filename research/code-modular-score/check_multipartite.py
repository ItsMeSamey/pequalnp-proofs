from itertools import product
from random import Random
def dp(parts,labels):
    initial=(0,0,(0,0,0))
    states={initial}
    for part in sorted(set(parts)):
        tmp={(x,y,cls,(0,0,0)) for x,y,cls in states}
        for v,p in enumerate(parts):
            if p!=part:continue
            nxt=set()
            for x,y,cls,cnt in tmp:
                for b in range(3):
                    zz=list(cnt);zz[b]=min(2,zz[b]+1)
                    nxt.add((x^(labels[v] if b==0 else 0),y^(labels[v] if b==1 else 0),cls,tuple(zz)))
            tmp=nxt
        states={(x,y,tuple(o if c==0 else c if o==0 else 3 for o,c in zip(cls,cnt))) for x,y,cls,cnt in tmp}
    return {(x,y) for x,y,cls in states if all(z in (1,3) for z in cls)}
def oracle(parts,labels):
    out=set()
    for bins in product(range(3),repeat=len(parts)):
        sums=[0,0,0]
        for j in range(3):
            vertices=[v for v,b in enumerate(bins) if b==j]
            if not vertices or (len(vertices)>1 and len({parts[v] for v in vertices})==1):break
            for v in vertices:sums[j]^=labels[v]
        else:out.add(tuple(sums[:2]))
    return out
rng=Random(616)
for _ in range(110):
    n=rng.randrange(1,8)
    p=[rng.randrange(4) for _ in range(n)]
    v=[rng.randrange(16) for _ in range(n)]
    assert dp(p,v)==oracle(p,v)
print('110 multipartite DP spectra match exhaustive connected partitions')
