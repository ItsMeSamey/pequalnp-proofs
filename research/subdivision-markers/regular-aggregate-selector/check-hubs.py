"""Whole-star comparison of arbitrary child tables and compiled proxy tables."""
from itertools import product
from random import Random
from check import actual
from triangle import triangle, image, canonical

def step(states,options,U,k):
    out={}
    for (a,b,t,L),cost in states.items():
        for (c,d),score,T,extra in options:
            if cost+extra>k:
                continue
            Z=L+tuple(image(U,x) for x in canonical(T))
            new=canonical(Z)
            if len(Z)!=len(new):
                continue
            key=(a^image(U,c),b^image(U,d),t^score,new)
            out[key]=min(out.get(key,cost+extra),cost+extra)
    return out

def run():
    rng=Random(8762)
    count=0
    for rep in range(12):
        k=rep%3
        original={(0,0,0,()):0}
        compiled=original.copy()
        for j in range(3+rep%3):
            cols=(1,2)+tuple(rng.randrange(4) for _ in range(rng.randrange(3)))
            U=(1,2)
            ext=(rng.randrange(1,8),0)
            ext=(ext[0],rng.choice([u for u in range(1,8) if u!=ext[0]]))
            tags=[(rng.randrange(1<<k),rng.randrange(1<<k)) for _ in cols]
            def score(colors):
                f=sum(bool(v&1)<<i for i,v in enumerate(colors))
                g=sum(bool(v&2)<<i for i,v in enumerate(colors))
                return image([a for a,b in tags],f)^image([b for a,b in tags],g)
            modes=set()
            for c in product(range(4),repeat=len(cols)):
                ans=actual(cols,U,c)
                if ans is not None:
                    ab,T=ans
                    modes.add((ab,score(c),T))
            _,chart=triangle(cols,U)
            proxy={(ab,score(colors),T,0) for ab,z,colors,T in chart}
            original=step(original,[(*s,0) for s in modes],ext,k)
            compiled=step(compiled,proxy|{(*s,1) for s in modes},ext,k)
        for K in [(),(1,),(2,3),(1,2,4)]:
            def admitted(S):
                return {(a,b,t) for (a,b,t,L) in S if len(canonical(K+L))==len(K)+len(L)}
            assert admitted(original)==admitted(compiled)
            count+=len(admitted(compiled))
    print('12 rank-two hub spectra, attainable imbalance/target/test records',count)

if __name__=='__main__':
    run()
