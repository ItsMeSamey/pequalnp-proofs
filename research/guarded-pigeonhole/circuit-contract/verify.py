"""Differential check of the mixed-score image for circuit contraction."""
from random import Random
def par(v):return v.bit_count()%2
def sums(seq):
    a=[0]
    for x in seq:a += [b^x for b in a]
    return a
def basis(vs):
    D={}
    for x in vs:
        while x and x.bit_length() in D:x ^= D[x.bit_length()]
        if x:D[x.bit_length()]=x
    return D
def models(vs,ls,us,r,condition=0):
    sx=sums(vs);wt=sums(ls);ans=set()
    for d in range(1<<r):
        forb=sum(par(d&v)<<i for i,v in enumerate(vs))
        if forb&condition:continue
        ds=sum(par(d&u)<<j for j,u in enumerate(us))
        ans.update(ds^wt[x] for x in range(len(sx)) if sx[x]==0 and not x&forb)
    return ans
def contract(vs,ls,us,S,r):
    T=[i for i in range(len(vs)) if S>>i&1];B=T[:-1]
    gen=[vs[i] for i in B];sig=[ls[i] for i in B];k=len(B)
    for j in range(r):
        if len(basis(gen+[1<<j]))>len(gen):gen.append(1<<j)
    co={v:x for x,v in enumerate(sums(gen))}
    sect=sums(sig);mask=(1<<k)-1
    outside=[i for i in range(len(vs)) if not S>>i&1]
    nv=[co[vs[i]]>>k for i in outside];nl=[ls[i]^sect[co[vs[i]]&mask] for i in outside]
    nu=[co[u]>>k for u in us];dl=sums(ls)[S]
    states=models(nv,nl,nu,r-k)
    return states|{s^dl for s in states}
if __name__=='__main__':
    rng=Random(49107);checks=0;witnesses=0
    for _ in range(550):
        r=rng.randrange(1,6);n=rng.randrange(r+1,9)
        vs=[rng.randrange(1<<r) for _ in range(n)];ls=[rng.randrange(16) for _ in vs]
        us=[rng.randrange(1<<r) for _ in range(4)];xs=sums(vs);ws=sums(ls)
        cs=[s for s in range(1,1<<n) if xs[s]==0 and ws[s] and len(basis(v for i,v in enumerate(vs) if s>>i&1))==s.bit_count()-1]
        if not cs:continue
        S=rng.choice(cs)
        assert contract(vs,ls,us,S,r)==models(vs,ls,us,r,S)
        checks+=1
        reps={v:vs.index(v) for v in set(vs) if v}
        short=[]
        for s in cs:
            T=[i for i in range(n) if s>>i&1]
            if len(T)<=2:short.append(s);continue
            if any(reps.get(vs[i])!=i for i in T):continue
            W=set(sums([vs[i] for i in T]))
            if not any(v in W and i not in T for v,i in reps.items()):short.append(s)
        pure={sum(par(d&u)<<j for j,u in enumerate(us)) for d in range(1<<r)}
        all_sc=models(vs,ls,us,r);via=set(pure)
        for s in short:via.update(contract(vs,ls,us,s,r))
        assert via==all_sc
        witnesses+=len(all_sc-pure)
    print(checks,'fixed-circuit and chordless-cover image checks;',witnesses,'non-pure-dual target occurrences')
