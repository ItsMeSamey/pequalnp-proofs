from itertools import combinations,product
from contextlib import redirect_stdout
from io import StringIO
from random import Random
with redirect_stdout(StringIO()):
    from disconnected import scalable,span_table
    from check import binary,mul,div,rankf
from relations import span

def check(s,gs,tstar,C,pins,b):
    n=len(s)
    sites=[(1<<i,0) for i in range(n)]+C
    def hblock(v,g):
        if g: return g
        return next((s[i] for i in range(n) if v>>i&1),1)
    groups=[[v<<2|g for v,g in sites if hblock(v,g)==h] for h in (1,2,3)]
    t,j=next((v,i) for i,(v,g) in enumerate(sites) if g==1)
    chart=[[a^(h if t>>i&1 else 0) for i,a in enumerate(binary(v,n))]+[h] for v,h in sites]
    assert scalable(chart)
    for (v,h),col in zip(sites,chart):
        assert all(z in (0,1) for z in [div(mul(f,x),h) for f,x in zip(s+[1],col)] ) if h else True
    # Compare actual N without the coloop, before pivoting, to [A;g].
    p,q=pins
    pp=p^(1<<n);w=[x|(y<<2) for x,y in zip(binary(pp,n+1),binary(q,n+1))]
    p0=b[0]|b[1]<<2
    N=[[x^div(mul(y,h),p0) for x,y in zip(binary(v,n+1),w)] for v,h in sites]
    for ids in combinations(range(len(sites)),n+1):
        assert rankf([N[i] for i in ids])==rankf([chart[i] for i in ids])
    K=span([(((pin&sum(1<<i for i,f in enumerate(s) if f==h))<<2)) for pin in pins for h in (1,2,3)]+[1,2,tstar<<2])
    dp={frozenset({0})}
    maxbound=0
    def palette(E):
        cells={frozenset({0})}
        for e in E: cells.update({frozenset(S|{x^e for x in S}) for S in cells})
        return {S&K for S in cells}
    for G in groups:
        bound=(len(span(G)&K)).bit_length()-1
        maxbound=max(maxbound,bound)
        assert bound<=3
        dp={span(x|y) for x in dp for y in palette(G)}
    assert dp==palette([v<<2|g for v,g in sites])
    tested=0;eq=False
    for ids in combinations(range(len(sites)),n):
        B=span_table([sites[i][0] for i in ids],[sites[i][1] for i in ids])
        if B is None:continue
        tested+=1
        success=(B[p],B[q])==b
        Nbasis=[N[i] for i in ids]+[binary(1<<n,n+1)]
        assert success==(rankf(Nbasis)<n+1)
        eq|=success
    lifted=any(not any(v in S for v in (1,2,3)) and p<<2|b[0] in S and q<<2|b[1] in S for S in dp)
    assert lifted==eq
    return len(dp),maxbound,tested,int(eq)

if __name__=='__main__':
    rng=Random(70)
    for three in (False,True):
        totals=[0]*4
        # Two-gain case has t*=4 and j0 carrying that cross-sector bit.
        s=[1,2,3,1]
        C=[(1,1),(8,1),(2,2),(4,3),(9,0)] if three else [(5,1),(12,1),(6,2),(9,0)]
        for _ in range(32):
            p=rng.randrange(16);q=rng.randrange(1,16)
            b=(rng.randrange(1,4),rng.randrange(1,4))
            obs=check(s,None,0 if three else 4,C,(p,q),b)
            totals=[a+c for a,c in zip(totals,obs)]
        print('gains',3 if three else 2,'cases 32; trace cells, summed max bounds, original bases, YES:',totals)
