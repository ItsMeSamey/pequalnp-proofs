"""Compare full child tables with star replacements and t exceptional children."""
from functools import lru_cache
from random import Random

@lru_cache(None)
def states(edges):
    n=1+max(max(e) for e in edges)
    cuts={sum((((S>>u)^(S>>v))&1)<<i for i,(u,v) in enumerate(edges)) for S in range(1<<n)}
    cyc=[]
    for C in range(1<<len(edges)):
        p=0
        for i,(u,v) in enumerate(edges):
            if C>>i&1:p^=(1<<u)^(1<<v)
        if not p:cyc.append(C)
    return [(C,D) for C in cyc for D in cuts]

def cost(C,D,A,B):
    v=0
    for j,(a,b) in enumerate(zip(A,B)):
        if C>>j&1:v^=a
        if D>>j&1:v^=b
    return v

def tables(A,B):
    E=((0,1),(1,2),(2,0),(3,4),(4,0),(3,1),(3,1),(3,2))
    out={}
    for C,D in states(E):
        if (C&D)>>3:continue
        out.setdefault((C&7,D&7),set()).add(cost(C>>3,D>>3,A,B))
    return out

rng=Random(38)
def check(t):
    roots=[(0,1,2),(0,3,4)]; real=[(1,3),(2,4)]
    label=lambda k:[rng.randrange(1<<t) for _ in range(k)]
    ra,rb=label(2),label(2)
    ca,cb=[label(5),label(5)],[label(5),label(5)]
    tab=[tables(a,b) for a,b in zip(ca,cb)]
    def spectrum(mask):
        E=real[:]; A=ra[:]; B=rb[:]; ports={}
        for j,(u,v,w) in enumerate(roots):
            a,b=ca[j],cb[j]
            if mask>>j&1:
                ports[j]=len(E); E.extend([(u,v),(v,w),(w,u)]); A.extend([0]*3);B.extend([0]*3)
            else:
                E.extend([(5+j,i) for i in (u,v,w)])
                A.extend([a[0]^a[1],a[2],a[4]])
                B.extend([b[1],b[2]^b[3],b[4]])
        virtual=sum(7<<p for p in ports.values())
        out=set()
        for C,D in states(tuple(E)):
            if C&D&~virtual:continue
            S={cost(C,D,A,B)}
            for j,p in ports.items():
                F=tab[j].get(((C>>p)&7,(D>>p)&7),set())
                S={x^y for x in S for y in F}
            out.update(S)
        return out
    expected=spectrum(3)
    assert expected==set().union(*(spectrum(m) for m in range(4) if m.bit_count()<=t))
for i in range(250):
    check(1+i%2)
K4=((0,1),(1,2),(2,0),(3,0),(3,1),(3,2))
T={}
for C,D in states(K4):
    if C&D or (C&7).bit_count()>1:continue
    T.setdefault((C&7,(D&7)<<3),set()).add((D>>3)&1)
assert len(T)==10
assert not any(all((((s|d)&coef).bit_count()%2) in v for (s,d),v in T.items()) for coef in range(64))
print("Verified 250 two-child glueings and all 64 linear baselines on the marked K4.")
