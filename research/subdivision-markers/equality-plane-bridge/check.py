"""Physical equality rank and exhaustive kernel checks."""
from itertools import combinations, product
from random import Random
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1]/'binary-aggregate-selector'))
from solver import apply, canonical, eliminate, image, solve

def compare(qdim,columns):
    # Ordinary raw columns are [private | target low two named | outside high two named].
    vdim=qdim+2
    full=(1<<vdim)-1
    Vtuple=tuple(c&full for c in columns)
    if len(canonical(x&((1<<qdim)-1) for x in Vtuple))!=qdim:
        return 0
    target=(1<<qdim,2<<qdim)
    def test(X):
        S=tuple(columns[i] for i in range(len(columns)) if X>>i&1)
        return all((solve(S,i<<qdim) is not None)==(i<4) for i in range(16))
    direct=any(test(X) for X in range(1<<len(columns)))
    equality=False
    inequality=False
    for h in product(range(1<<qdim),repeat=2):
        equal=tuple(x for x,c in zip(Vtuple,columns) if apply(h,x)==c>>vdim)
        uneq=tuple(x for x,c in zip(Vtuple,columns) if apply(h,x)!=c>>vdim)
        equality|=len(canonical(equal))==vdim
        inequality|=len(canonical(uneq))==vdim
    assert direct==equality
    return direct,inequality

def graph(L):
    # A=0, B=1, rim vertices 2,..,L+1. The first L+1 edges form A's star.
    return [(0,i) for i in range(1,L+2)]+[(1,i+2) for i in range(L)]+[(i+2,(i+1)%L+2) for i in range(L)]

def signs(L,y):
    E=graph(L)
    n=L+2
    gauge=sum(((y>>i)&1)<<v for i,(u,v) in enumerate(E[:L+1]))
    delta=sum(((((gauge>>u)^(gauge>>v))&1)<<e) for e,(u,v) in enumerate(E))
    norm=y^delta
    if not norm:
        return None
    rim=(1<<L)-1
    S=(norm>>(L+1))&rim
    R=(norm>>(2*L+1))&rim
    if S:
        choose=(S&-S).bit_length()-1
        b=(rim^(1<<choose))<<2
    else:
        # Removing an edge signed one leaves a path; alternate b along that path.
        e=(R&-R).bit_length()-1
        b=1<<1
        for j in range(L):
            if j%2:
                b|=1<<(2+(e+1+j)%L)
    # Solve for a on the two same-b classes; every required signed parity is linear.
    cs=[]; values=0
    for i,(u,v) in enumerate(E):
        if ((b>>u)^(b>>v))&1==0:
            values|=(1^((norm>>i)&1))<<len(cs)
            cs.append((1<<u)^(1<<v))
    from solve import functional
    a=functional(cs,values)
    assert a is not None
    return a^gauge,b

def physical(L,y,w):
    E=graph(L); n=L+2
    a,b=w
    active=[1<<i for i in range(n)]
    for j,(u,v) in enumerate(E):
        t=(1<<u)^(1<<v)^(1<<(n+j))
        if apply((a|(y<<n),b),t):
            active.append(t)
    assert len(canonical(active))==len(E)+n

def run():
    rng=Random(881)
    agree=opposite=0
    for rep in range(130):
        d=rep%3
        cols=[rng.randrange(1<<(d+4)) for _ in range(rng.randrange(2,9))]
        r=compare(d,cols)
        if r!=0:
            agree+=1
            opposite+=r[0]!=r[1]
    counts={}
    for L in (3,5,7):
        total=0
        for s in range(1,1<<(2*L)):
            y=s<<(L+1)
            w=signs(L,y)
            assert w is not None
            physical(L,y,w)
            total+=1
        counts[L]=total
        E=graph(L)
        for j in range(20):
            y=rng.randrange(1<<len(E))
            w=signs(L,y)
            if w is not None:
                physical(L,y,w)
    print('raw four-name comparisons',agree,'inequality disagreed',opposite)
    print('all nonzero private cycle syndromes by odd rim',counts)

if __name__=='__main__':
    run()
