"""Raw-function, raw-word and physical named-kernel checks."""
from itertools import product
from random import Random
from solver import aggregate, extend, apply, canonical, eliminate, image, solve

def dual(cols):
    _,C=eliminate(cols)
    return tuple(sum(((c>>i)&1)<<j for j,c in enumerate(C)) for i in range(len(cols)))

def feasible(T,o,P,v,h):
    return all(apply(h,p)==x for p,x in zip(P,v)) and len(canonical(a for a,k in zip(T,o) if apply(h,a)!=k))==len(canonical(T))

def pinned(T,o,P,v,stats):
    nbits=max((x.bit_length() for x in T),default=0)
    ref=next((h for h in product(range(1<<nbits),repeat=2) if feasible(T,o,P,v,h)),None)
    h=extend(tuple(T),tuple(o),tuple(P),tuple(v),stats)
    assert (ref is None)==(h is None)
    if h is not None:
        assert feasible(T,o,P,v,h)

def physical(D,tags,k,t,f,g):
    m=len(D)
    d=max((v.bit_length() for v in D),default=0)
    shift=m+2*d
    chosen=[]
    for j,(a,(u,v)) in enumerate(zip(D,tags)):
        c=((f>>j)&1)+2*((g>>j)&1)
        for w in range(1,4):
            if not c or c==w:
                col=1<<j
                if w&1:
                    col^=(a<<m)^(u<<shift)
                if w&2:
                    col^=(a<<(m+d))^(v<<shift)
                chosen.append(col)
    r=((1<<m)-1)^(t<<shift)
    tagroots=tuple(1<<(shift+j) for j in range(k))
    assert solve(chosen,r) is not None
    assert len(canonical(tuple(chosen)+tagroots))==len(canonical(chosen))+k

def host(D,tags,k,stats):
    C=eliminate(D)[1]
    words=[image(C,i) for i in range(1<<len(C))]
    full=(1<<len(D))-1
    ref=set()
    for f,g in product(words,repeat=2):
        z=[a for e,a in enumerate(D) if not ((f|g)>>e&1)]
        if len(canonical(z))==len(z):
            ref.add(image([a for a,b in tags],f)^image([b for a,b in tags],g))
    for t in range(1<<k):
        actual=aggregate(D,tags,k,t,stats)
        assert (actual is not None)==(t in ref)
        if actual is not None:
            f,g=actual
            assert image(D,f)==image(D,g)==0
            assert image([a for a,b in tags],f)^image([b for a,b in tags],g)==t
            assert len(canonical(a for e,a in enumerate(D) if not ((f|g)>>e&1)))==(full^(f|g)).bit_count()
            physical(D,tags,k,t,f,g)
    return len(ref)

def run():
    rng=Random(2601)
    stats={}
    for rep in range(160):
        r=rep%6
        T=tuple(1<<i for i in range(r))+tuple(rng.randrange(1<<r) for _ in range(rng.randrange(5)))
        P=canonical(rng.randrange(1<<r) for _ in range(rng.randrange(r+1)))
        pinned(T,[rng.randrange(4) for e in T],P,[rng.randrange(4) for p in P],stats)
    pinned((0,1,1,2,3),(0,1,2,3,0),(1,2),(0,0),stats)
    pinned((0,0),(1,2),(),(),stats)
    pinned((1,2,4),(0,0,0),(1,2,4),(0,0,0),stats)
    print('163 affine-offset pin scenarios',stats)
    stats={}
    hosts=queries=hits=0
    F7=tuple(range(1,8))
    K33=tuple((1<<i)^(1<<j) for i in range(3) for j in range(3,6))
    for name,D in [('F7',F7),('F7*',dual(F7)),('M*(K3,3)',dual(K33))]:
        tags=[(rng.randrange(8),rng.randrange(8)) for _ in D]
        h=host(D,tags,3,stats)
        print(name,h,'of 8 targets')
        hosts+=1
        queries+=8
        hits+=h
    for j in range(60):
        k=j%5
        m=rng.randrange(7)
        d=rng.randrange(1,5)
        D=tuple(rng.randrange(1<<d) for _ in range(m))
        tags=tuple((rng.randrange(1<<k),rng.randrange(1<<k)) for e in D)
        hits+=host(D,tags,k,stats)
        queries+=1<<k
        hosts+=1
    print('hosts',hosts,'targets',queries,'physical witnesses',hits,stats)

if __name__=='__main__':
    run()
