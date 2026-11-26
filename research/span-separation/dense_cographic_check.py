from random import Random

def closure(vs):
    out={0}
    for v in vs: out |= {a^v for a in out}
    return frozenset(out)

def connected(B,E):
    seen={B[0]}
    for _ in B:
        for u,v,s in E:
            if u in B and v in B and (u in seen or v in seen):seen.update((u,v))
    return len(seen)==len(B)

def parts(n):
    def grow(i,p):
        if n==i:
            yield tuple(tuple(B) for B in p);return
        for j in range(len(p)):
            p[j].append(i);yield from grow(i+1,p);p[j].pop()
        p.append([i]);yield from grow(i+1,p);p.pop()
    yield from grow(0,[])

def compare(n,E):
    gam=[0]*n
    for u,v,s in E:gam[u]^=s;gam[v]^=s
    d=max(n-1-sum(i in (a,b) for a,b,_ in E) for i in range(n))
    def label(B):
        a=0
        for v in B:a^=gam[v]
        return a
    exact=set();small=set()
    for part in parts(n):
        if any(not connected(B,E) for B in part):continue
        H=closure(label(B) for B in part);exact.add(H)
        if len(part)==len(H).bit_length():small.add(H)
    assert exact==small
    for i in range(1,1<<n):
        B=tuple(v for v in range(n) if i>>v&1)
        if len(B)>2*d:assert connected(B,E)
    cuts=[]
    for S in range(1<<(n-1)):
        mask=val=0
        for j,(a,b,l) in enumerate(E):
            if (S>>a ^ S>>b)&1:mask|=1<<j;val^=l
        cuts.append((mask,val))
    direct={frozenset(l for mask,l in cuts if mask&~X==0) for X in range(1<<len(E))}
    assert exact==direct

rng=Random(579)
for _ in range(180):
    n=rng.randrange(2,6)
    E=[(i,j,rng.randrange(16)) for i in range(n) for j in range(i+1,n)
       if j==i+1 or rng.randrange(2)]
    compare(n,E)
print('180 exact cographic catalogs, partition sizes and density cutoffs checked')
