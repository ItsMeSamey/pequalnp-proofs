"""Check every proxy on small binary limbs and all physical colorings."""
from itertools import product
from random import Random
from collections import Counter
from triangle import triangle, image, solve, canonical

def actual(cols,U,colors):
    f=sum(bool(v&1)<<i for i,v in enumerate(colors))
    g=sum(bool(v&2)<<i for i,v in enumerate(colors))
    z=tuple(c for c,v in zip(cols,colors) if not v)
    if len(canonical(z))!=len(z):
        return None
    a,b=solve(U,image(cols,f)),solve(U,image(cols,g))
    if a is None or b is None:
        return None
    return (a,b),frozenset(u for u in range(4) if solve(z,image(U,u)) is not None)

def run():
    rng=Random(317740)
    groups=Counter()
    lifts=tests=0
    for i in range(150):
        d=rng.randrange(2,5)
        cols=tuple(1<<j for j in range(d))+tuple(rng.randrange(1<<d) for _ in range(rng.randrange(4)))
        p=rng.randrange(1,1<<d)
        q=rng.choice([v for v in range(1,1<<d) if v!=p])
        U=(p,q)
        mode,records=triangle(cols,U)
        groups[mode]+=1
        available={}
        for ab,z,colors,T in records:
            ans=actual(cols,U,colors)
            assert ans is not None and ans[0]==ab and ans[1]<=T
            available.setdefault(ab,set()).add(T)
            lifts+=1
        for colors in product(range(4),repeat=len(cols)):
            ans=actual(cols,U,colors)
            if ans is not None:
                ab,L=ans
                assert any(T<=L for T in available[ab])
                tests+=1
        assert len(available)==16
    print(dict(groups),'proxy lifts',lifts,'feasible physical tuples',tests)

if __name__=='__main__':
    run()
