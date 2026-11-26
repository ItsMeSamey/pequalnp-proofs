from random import Random
from itertools import combinations

def par(v):return v.bit_count()%2

def combosum(cols,s):
    result=0
    for i,c in enumerate(cols):
        if s>>i&1:result^=c
    return result

def run(cols,r,p,rr,b,h):
    n=len(cols)
    cycles=[x for x in range(1<<n) if combosum(cols,x)==0 and par(p&x)]
    covecs=[(sum(par(w&c)<<i for i,c in enumerate(cols)),par(w&h)) for w in range(1<<r) if par(w&b)]
    full=set()
    badrect=False
    for x in cycles:
        spectra={s for d,s in covecs if d&x==0}
        if len(spectra)==2:badrect=True
        full|={par(rr&x)^s for s in spectra}
    for d,_ in covecs:
        if len({par(rr&x) for x in cycles if not x&d})==2:badrect=True
    lifted=[c|(((p>>i)&1)<<r) for i,c in enumerate(cols)]
    u=1<<r
    out=set()
    for T in combinations(range(n),r):
        B=[lifted[i] for i in T]+[b]
        inv={combosum(B,s):s for s in range(1<<(r+1))}
        if len(inv)!=1<<(r+1):continue
        xu=inv[u]
        if xu>>r:continue
        weights=sum(((rr>>i)&1)<<j for j,i in enumerate(T))
        out.add(par(weights&xu)^(inv[h]>>r))
    return full,out,badrect

if __name__=='__main__':
    rng=Random(411)
    unfiltered=0
    for _ in range(2500):
        r=rng.randrange(1,5);n=rng.randrange(r+1,r+5)
        cols=[1<<i for i in range(r)]+[rng.randrange(1<<r) for _ in range(n-r)]
        p=rng.randrange(1<<n);rr=rng.randrange(1<<n)
        b=rng.randrange(1,1<<r);h=rng.randrange(1<<r)
        full,out,bad=run(cols,r,p,rr,b,h)
        assert out<=full
        assert bad or full==out
        if full!=out:unfiltered+=1
    print('2500 primary cases checked; excluding full-side rectangles matters in',unfiltered,'cases.')
