"""All terminal traces versus all original disjoint pairs on binary matrices."""
from random import Random
from two import span
from solver import marker

def main():
    rng=Random(89921)
    for _ in range(130):
        n,r,t=rng.randrange(1,8),rng.randrange(1,5),rng.randrange(1,4)
        h=[rng.randrange(1<<r) for _ in range(n)]
        a,b=([rng.randrange(1<<t) for _ in h] for _ in range(2))
        dual=span([sum(1<<i for i,v in enumerate(h) if v>>j&1) for j in range(r)])
        want={(marker(a,c),marker(b,d)) for c in range(1<<n) for d in dual
              if not c&d and not marker(h,c)}
        real=[v|(w<<r) for v,w in zip(h,a)]
        dualterms=[marker(h,sum(1<<i for i,v in enumerate(b) if v>>j&1)) for j in range(t)]
        got=set()
        for X in range(1<<n):
            selected=[v for i,v in enumerate(real) if X>>i&1]
            V=span(selected)
            ps=[p for p in range(1<<t) if p<<r in V]
            qs={sum(((u&v).bit_count()%2)<<j for j,v in enumerate(dualterms))
                for u in range(1<<r) if all(not (u&v).bit_count()%2 for v in selected)}
            got.update((p,q) for p in ps for q in qs)
        assert got==want
    print("130 full terminal trace tables agree")
if __name__=="__main__":
    main()
