from random import Random
from itertools import product

def span_rank(vs):
    p={}
    for v in vs:
        while v and v.bit_length() in p:v^=p[v.bit_length()]
        if v:p[v.bit_length()]=v
    return len(p)
def qval(x,c,l,rows):
    return (c+(x&l).bit_count()+sum((x&r).bit_count() for i,r in enumerate(rows) if x>>i&1))%2
def sumblock(q,blocks,clauses):
    c,l,R=q
    n=len(R);M=[R[i]|sum(((r>>i)&1)<<j for j,r in enumerate(R)) for i in range(n)]
    future=(1<<n)-1;D={0:(-1)**c}
    for bl in blocks:
        bm=sum(1<<j for j in bl);newfuture=future^bm
        local=[cl for cl in clauses if not ((cl[0]|cl[1])&~bm)]
        nxt={}
        for digits in product((0,1),repeat=len(bl)):
            b=sum(d<<j for d,j in zip(digits,bl))
            if any(not ((b&a)|(~b&z)) for a,z in local):continue
            phase=qval(b,0,l,R)
            add=0
            for j,d in zip(bl,digits):
                if d:add^=M[j]&newfuture
            for u,v in D.items():
                un=(u&newfuture)^add
                nxt[un]=nxt.get(un,0)+v*(-1)**(phase+(u&b).bit_count())
        rho=span_rank(M[j]&newfuture for j in range(n) if not newfuture>>j&1)
        assert len(nxt)<=2**rho
        D=nxt;future=newfuture
    return D.get(0,0)
rng=Random(93)
for rep in range(200):
    n=rng.randrange(3,10);k=rng.randrange(1,5)
    bl=[list(range(i,min(i+2,n))) for i in range(0,n,2)]
    clauses=[]
    for b in bl:
        if rng.randrange(2):
            mask=sum(1<<i for i in b);pos=rng.randrange(1<<n)&mask
            clauses.append((pos,mask^pos))
    polys=[(rng.randrange(2),rng.randrange(1<<n),[rng.randrange(1<<n)&~((2<<i)-1) for i in range(n)]) for _ in range(k)]
    total=0
    for a in range(1<<k):
        c=l=0;rows=[0]*n
        for j,(q,v,R) in enumerate(polys):
            if a>>j&1:
                c^=q;l^=v;rows=[x^y for x,y in zip(rows,R)]
        total+=sumblock((c,l,rows),bl,clauses)
    count=sum(all((x&p)|(~x&z) for p,z in clauses) and not any(qval(x,*q) for q in polys) for x in range(1<<n))
    assert total==count*(1<<k)
print('200 constrained quadratic systems match raw counts; all per-character cut-state rank bounds checked')
