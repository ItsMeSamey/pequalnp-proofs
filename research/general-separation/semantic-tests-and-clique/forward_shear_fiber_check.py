"""Brute-force radicals, candidate translations, and final primary preimages."""
from random import Random

def val(row,u,z=0):
    a,f,c=row
    return ((a&u).bit_count()+(f&z).bit_count()+c)%2

def check(q,reads,output,upgrade=False):
    m=len(reads)//2
    raw=reads.copy()
    full=[]
    for x in range(1<<q):
        z=0
        for i in range(m):
            z |= (val(raw[2*i],x,z)&val(raw[2*i+1],x,z))<<i
        full.append(val(output,x,z))
    rows=reads+[output]
    n=q
    eqs=[]
    lift=list(range(1<<q))
    absorbed=0
    upgraded=False
    retained=0
    for i in range(m):
        a,b=rows[:2]
        rows=rows[2:]
        assert not (a[1] or b[1])
        p=[val(a,u)&val(b,u) for u in range(1<<n)]
        if not a[0] or not b[0] or a[0]==b[0]:
            mask=sum((p[1<<j]^p[0])<<j for j in range(n))
            assert all(val((mask,0,p[0]),u)==p[u] for u in range(1<<n))
            rows=[(l^(mask if f>>i&1 else 0), f&~(1<<i), c^(p[0] if f>>i&1 else 0)) for l,f,c in rows]
            continue
        active=[u for u,bit in enumerate(p) if bit]
        accepted=[]
        strict=[]
        for v in range(1<<n):
            if val((a[0],0,0),v) or val((b[0],0,0),v):continue
            if any((mask&v).bit_count()%2 != (future>>i&1) for mask,future,c in rows):continue
            gradients=[]
            kappas=[]
            for e in eqs:
                delta=[e[u^v]^e[u] for u in range(1<<n)]
                grad=sum((delta[1<<j]^delta[0])<<j for j in range(n))
                allowed=grad in (0,a[0],b[0],a[0]^b[0])
                assert allowed==(len({delta[u] for u in active})==1)
                gradients.append(grad)
                kappas.append(delta[active[0]])
            if all(g in (0,a[0],b[0],a[0]^b[0]) for g in gradients):
                accepted.append((v,kappas))
            if not any(gradients):strict.append(v)
        if accepted:
            v,kappas=accepted[0]
            upgraded |= not strict and any(kappas)
            absorbed+=1
            eqs=[[bit^(k&pu) for bit,pu in zip(e,p)] for e,k in zip(eqs,kappas)]
            lift=[u^(v if p[u] else 0) for u in lift]
            rows=[(mask,f&~(1<<i),c) for mask,f,c in rows]
        else:
            retained+=1
            rows=[(mask|(((f>>i)&1)<<n),f&~(1<<i),c) for mask,f,c in rows]
            eqs=[e+e for e in eqs]+[p+[b^1 for b in p]]
            lift=[u|(p[u]<<n) for u in lift]
            n+=1
        assert set(lift)=={u for u in range(1<<n) if all(not e[u] for e in eqs)}
        assert len(set(lift))==len(lift)
    assert [val(rows[0],u) for u in lift]==full
    assert not upgrade or upgraded
    return absorbed,retained

rng=Random(804)
tot=[0,0]
for _ in range(90):
    q,m=3,5
    rows=[(rng.randrange(1<<q),rng.randrange(1<<(i//2)),rng.randrange(2)) for i in range(2*m)]
    result=check(q,rows,(rng.randrange(1<<q),rng.randrange(1<<m),rng.randrange(2)))
    tot=[x+y for x,y in zip(tot,result)]
# Repeated reversible Toffoli updates of three bits: affine formal register masks.
state=[(1,0,0),(2,0,0),(4,0,0)]
rows=[]
for i in range(15):
    j=i%3
    rows.extend([state[(j+1)%3],state[(j+2)%3]])
    a,f,c=state[j]
    state[j]=(a,f^(1<<i),c)
assert check(3,rows,state[0])==(15,0)
# Reconverging chain of two equal products, canceled at every update.
rows=[]
for i in range(12):
    rows.extend([(1,0,0),(2,0,0)])
assert check(3,rows,(4,(1<<12)-1,0))==(12,0)
print('90 random systems, forward bijections after every gate; absorbed/retained',tot,'plus 27 structured gates')

# z0=xy is retained because the second gate directly reads z0.
# Its next product yz0 can translate x, with D_x(z0+xy)=y=1 on the fiber.
assert check(2,[(1,0,0),(2,0,0),(2,0,0),(0,1,0)],(1,2,0),True)==(1,1)
# Negated y on BOTH products, and final affine offset.
assert check(2,[(1,0,1),(2,0,1),(2,0,1),(0,1,0)],(1,2,1),True)==(1,1)
for offset in (0,1):
    for b in ((0,0,0),(0,0,1),(1,0,offset),(1,0,1-offset)):
        assert check(2,[(1,0,offset),b],(0,1,1))==(0,0)
print('2 forced nonradical upgrades with nonzero kappa; 8 affine controls passed')
